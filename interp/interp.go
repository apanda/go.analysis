// Package exp/ssa/interp defines an interpreter for the SSA
// representation of Go programs.
//
// This interpreter is provided as an adjunct for testing the SSA
// construction algorithm.  Its purpose is to provide a minimal
// metacircular implementation of the dynamic semantics of each SSA
// instruction.  It is not, and will never be, a production-quality Go
// interpreter.
//
// The following is a partial list of Go features that are currently
// unsupported or incomplete in the interpreter.
//
// * Unsafe operations, including all uses of unsafe.Pointer, are
// impossible to support given the "boxed" value representation we
// have chosen.
//
// * The reflect package is only partially implemented.
//
// * "sync/atomic" operations are not currently atomic due to the
// "boxed" value representation: it is not possible to read, modify
// and write an interface value atomically.  As a consequence, Mutexes
// are currently broken.  TODO(adonovan): provide a metacircular
// implementation of Mutex avoiding the broken atomic primitives.
//
// * recover is only partially implemented.  Also, the interpreter
// makes no attempt to distinguish target panics from interpreter
// crashes.
//
// * map iteration is asymptotically inefficient.
//
// * the equivalence relation for structs doesn't skip over blank
// fields.
//
// * the sizes of the int, uint and uintptr types in the target
// program are assumed to be the same as those of the interpreter
// itself.
//
// * all values occupy space, even those of types defined by the spec
// to have zero size, e.g. struct{}.  This can cause asymptotic
// performance degradation.
//
// * os.Exit is implemented using panic, causing deferred functions to
// run.
package interp

import (
	"fmt"
	"go/ast"
	"go/token"
	"os"
	"reflect"
	"runtime"
    "sync"
    "strings"
    "sync/atomic"
	"code.google.com/p/go.tools/go/types"
	"code.google.com/p/go.tools/ssa"
)

type status int

const (
	stRunning status = iota
	stComplete
	stPanic
)

type continuation int

const (
	kNext continuation = iota
	kReturn
	kJump
)

// Mode is a bitmask of options affecting the interpreter.
type Mode uint

const (
	DisableRecover Mode = 1 << iota // Disable recover() in target programs; show interpreter crash instead.
	EnableTracing                   // Print a trace of all instructions as they are interpreted.
)

// State shared between all interpreted goroutines.
type interpreter struct {
	prog           *ssa.Program         // the SSA program
	globals        map[ssa.Value]*value // addresses of global variables (immutable)
	mode           Mode                 // interpreter options
	reflectPackage *ssa.Package         // the fake reflect package
	errorMethods   ssa.MethodSet        // the method set of reflect.error, which implements the error interface.
	rtypeMethods   ssa.MethodSet        // the method set of rtype, which implements the reflect.Type interface.
    writer         *os.File
    wg             sync.WaitGroup
    gprefix        string
    fcount         uint64
    gcount         uint64
    gvars          map[ssa.Value] string
}

type frame struct {
	i                *interpreter
	caller           *frame
	fn               *ssa.Function
	block, prevBlock *ssa.BasicBlock
	env              map[ssa.Value]value // dynamic values of SSA variables
	locals           []value
	defers           []func()
	result           value
    resultSource     []string
	status           status
	panic            interface{}
    instrCount       uint64
    labels           map[ssa.Instruction] uint64
    packetType       string
    fprefix          string
    fvars            map[ssa.Value] string
    fcount           uint64
}

func (fr *frame) get(key ssa.Value) value {
	switch key := key.(type) {
	case nil:
		// Hack; simplifies handling of optional attributes
		// such as ssa.Slice.{Low,High}.
		return nil
	case *ssa.Function, *ssa.Builtin:
		return key
	case *ssa.Literal:
		return literalValue(key)
	case *ssa.Global:
		if r, ok := fr.i.globals[key]; ok {
			return r
		}
	}
	if r, ok := fr.env[key]; ok {
		return r
	}
	panic(fmt.Sprintf("get: no value for %T: %v", key, key.Name()))
}

func (fr *frame) String(key ssa.Value) string {
	switch key := key.(type) {
	case nil:
		// Hack; simplifies handling of optional attributes
		// such as ssa.Slice.{Low,High}.
		return ""
	case *ssa.Function, *ssa.Builtin:
        return fmt.Sprintf("%v", key)
	case *ssa.Literal:
		return fmt.Sprintf("%v", literalValue(key))
	case *ssa.Global:
        return fr.i.gvars[key]
	}
    //fmt.Fprintf(os.Stdout, "%v\n", reflect.TypeOf(key))
    //panic("Should never get here, boom")
    return fr.fvars[key] 
}

func (fr *frame) makeVar(key ssa.Value) string {
    vcount := atomic.AddUint64(&fr.fcount, 1)
    vname := fmt.Sprintf("%s_%d", fr.fprefix, vcount)
    fr.fvars[key] = vname
    return vname
}

func (fr *frame) aliasVar(newKey ssa.Value, oldKey ssa.Value) string {
    fr.fvars[newKey] = fr.fvars[oldKey]
    return fr.fvars[newKey]
}

func (fr *frame) rundefers() {
	for i := range fr.defers {
		if fr.i.mode&EnableTracing != 0 {
			fmt.Fprintln(os.Stdout, "Invoking deferred function", i)
		}
		fr.defers[len(fr.defers)-1-i]()
	}
	fr.defers = fr.defers[:0]
}

// findMethodSet returns the method set for type typ, which may be one
// of the interpreter's fake types.
func findMethodSet(i *interpreter, typ types.Type) ssa.MethodSet {
	switch typ {
	case rtypeType:
		return i.rtypeMethods
	case errorType:
		return i.errorMethods
	}
	return i.prog.MethodSet(typ)
}

// hashing an instruction is something we are going to be doing a lot, this just
// makes it easier to do this
func hashInstr (fr *frame, instr ssa.Instruction) uint64 {
    if fr.labels[instr] == 0 {
        fr.instrCount += 1
        fr.labels[instr] = fr.instrCount
    }
   return fr.labels[instr]
}

// recvTraditional implements the original channel receive functionality from unop
// in ops.go. This function essentially does a real channel receive (the interpreter represents
// channels as real Go objects).
func recvTraditional(instr *ssa.UnOp, x value) value {
    v, ok := <-x.(chan value)
    if !ok {
        v = zero(instr.X.Type().Underlying().(*types.Chan).Elem())
    }
    if instr.CommaOk {
        v = tuple{v, ok}
    }
    return v 
}

// recv is called by unop for channel receives. recv (currently) interposes to check if the channel is attempting to receive
// a packet or some other type, and injects packets into the stream.
// TODO: Better packet generation
func recv(fr *frame, instr *ssa.UnOp, x value) (value, string) {
    if (strings.HasSuffix(instr.X.Type().Underlying().(*types.Chan).Elem().String(), "github.com/apanda/learn.Packet")) {
        var v2 value
        switch instr.X.Type().Underlying().(*types.Chan).Elem().(type) {
            case *types.Pointer:
                v := new(value)
                *v = zero(instr.X.Type().Underlying().(*types.Chan).Elem().Deref())
                v2 = v
            default:
                v2 = zero(instr.X.Type().Underlying().(*types.Chan).Elem())
        } 
        if instr.CommaOk {
            v2 = tuple{v2, true}
        }
        return v2, "Packet"
    } else {
        return recvTraditional(instr, x), fr.String(instr.X)
    }
}

//sendTraditional implements the send functionality original implemented by visitInstr
func sendTraditional(fr *frame, instr *ssa.Send) {
    fr.get(instr.Chan).(chan value) <- copyVal(fr.get(instr.X))
}

// send is called by visitInstr to send a message. Here we make sure that if this happens to be a rule
// the interpreter just consumes it. Perhaps we should print out the rule or something else.
func send(fr *frame, instr *ssa.Send) {
    if fr.packetType != "" && strings.HasSuffix(instr.Chan.Type().Underlying().(*types.Chan).Elem().String(), fr.packetType) {
        // NOP, we already saw the construction of this rule
    } else {
        sendTraditional (fr, instr)
    }
}

// visitInstr interprets a single ssa.Instruction within the activation
// record frame.  It returns a continuation value indicating where to
// read the next instruction from.
func visitInstr(i *interpreter, fr *frame, instr ssa.Instruction, trace bool) continuation {
    //if trace {
    //    fmt.Fprintf(i.writer, "%v    ", reflect.TypeOf(instr))
    //}
	switch instr := instr.(type) {
	case *ssa.UnOp:
        if instr.Op == token.ARROW {
            var rside string
            fr.env[instr], rside = recv(fr, instr, fr.get(instr.X))
            if trace {
                fmt.Fprintf(i.writer, "<<%v = %v(%v) [%v]>>\n", fr.makeVar(instr), instr.Op, rside, fr.env[instr])
            }
        } else {
            fr.env[instr] = unop(instr, fr.get(instr.X))
            if trace {
                fmt.Fprintf(i.writer, "<<%v = %v(%v) [%v]>>\n", fr.makeVar(instr), instr.Op, fr.String(instr.X), fr.env[instr])
            }
        }

	case *ssa.BinOp:
		fr.env[instr] = binop(instr.Op, fr.get(instr.X), fr.get(instr.Y))
        if trace {
            fmt.Fprintf(i.writer, "<<%v = %v %v %v [%v]>>\n",
                        fr.makeVar(instr), fr.String(instr.X), instr.Op, fr.String(instr.Y), fr.env[instr])
        }
	case *ssa.Call:
        if trace {
            fmt.Fprintf(i.writer, "enter %v\n", fr.String(instr.Call.Func))
        }
		fn, args, argSrc := prepareCall(fr, &instr.Call)
        fnAsFun, ok := fn.(*ssa.Function)
        if ok && fnAsFun.FullName() == "github.com/apanda/constraints.Constraint" {
            fmt.Fprintln(i.writer, "Found constraint code")
        } else if ok && fnAsFun.FullName() == "github.com/apanda/constraints.PacketType" {
            arg := fr.get(instr.Call.Args[0])
            fmt.Fprintf(i.writer, "PacketType specified is %v\n", arg.(iface).t.Deref().String())
            fr.packetType = arg.(iface).t.Deref().String()
        } else {
            //Enter
            // Determine arguments
            var rets []string
            fr.env[instr], rets = call(fr.i, fr, instr.Pos(), fn, args, argSrc, trace)
            //Exit
            if trace {
                fmt.Fprintf(i.writer, "<<%v = %v [%v]>>\n", fr.makeVar(instr), rets, fr.env[instr])
            }
        }

	case *ssa.ChangeInterface:
		x := fr.get(instr.X)
		if x.(iface).t == nil {
			panic(fmt.Sprintf("interface conversion: interface is nil, not %s", instr.Type()))
		}
		fr.env[instr] = x
        if trace {
            fr.aliasVar(instr, instr.X)
            //fmt.Fprintf(i.writer, "<<%v = %v [%v]>>\n", , instr, fr.env[instr])
        } 
	case *ssa.ChangeType:
		fr.env[instr] = fr.get(instr.X) // (can't fail)
        if trace {
            fr.aliasVar(instr, instr.X)
        }

	case *ssa.Convert:
		fr.env[instr] = conv(instr.Type(), instr.X.Type(), fr.get(instr.X))
        if trace {
            fr.aliasVar(instr, instr.X)
        }

	case *ssa.MakeInterface:
		fr.env[instr] = iface{t: instr.X.Type(), v: fr.get(instr.X)}
        if trace {
            fr.aliasVar(instr, instr.X)
            //fmt.Fprintf(i.writer, "<<%v = %v [%v]>>\n", fr.makeVar(instr), fr.String(instr.X), fr.env[instr])
        }

	case *ssa.Extract:
		fr.env[instr] = fr.get(instr.Tuple).(tuple)[instr.Index]
        if trace {
            fmt.Fprintf(i.writer, "<<%v = %v[%v] [%v]>>\n", fr.makeVar(instr), fr.String(instr.Tuple), instr.Index, fr.env[instr])
        }

	case *ssa.Slice:
		fr.env[instr] = slice(fr.get(instr.X), fr.get(instr.Low), fr.get(instr.High))
        if trace {
            fmt.Fprintf(i.writer, "<<%v = %v [%v]>>\n", fr.makeVar(instr), fr.env[instr])
        }

	case *ssa.Ret:
        // Deal with this
		switch len(instr.Results) {
		case 0:
		case 1:
			fr.result = fr.get(instr.Results[0])
            fr.resultSource = append(fr.resultSource, fr.String(instr.Results[0]))
		default:
			var res []value
			for _, r := range instr.Results {
				res = append(res, fr.get(r))
                fr.resultSource = append(fr.resultSource, fr.String(r))
			}
			fr.result = tuple(res)
		}
		return kReturn

	case *ssa.RunDefers:
		fr.rundefers()

	case *ssa.Panic:
		panic(targetPanic{fr.get(instr.X)})

	case *ssa.Send:
        send(fr, instr)
        if trace {
            fmt.Fprintf(i.writer, "<<%v <- %v>>\n", fr.String(instr.Chan), fr.String(instr.X))
        }

	case *ssa.Store:
        if trace {
            fmt.Fprintf (i.writer, "<<*%v = %v [%v]>>\n", fr.String(instr.Addr), fr.String(instr.Val), fr.get(instr.Val)) 
        }
		*fr.get(instr.Addr).(*value) = copyVal(fr.get(instr.Val))

	case *ssa.If:
		succ := 1
		if fr.get(instr.Cond).(bool) {
			succ = 0
		}
        if trace {
            fmt.Fprintf (i.writer, "<<if %v then %v else %v [%v %v]>>\n", fr.String(instr.Cond), 
                fr.block.Succs[0], fr.block.Succs[1],  fr.get(instr.Cond).(bool), fr.block.Succs[succ])
        }
		fr.prevBlock, fr.block = fr.block, fr.block.Succs[succ]
		return kJump

	case *ssa.Jump:
		fr.prevBlock, fr.block = fr.block, fr.block.Succs[0]
		return kJump

	case *ssa.Defer:
		pos := instr.Pos() // TODO(gri): workaround for go/types bug in typeswitch+funclit.
		fn, args, argSrc := prepareCall(fr, &instr.Call)
		fr.defers = append(fr.defers, func() { call(fr.i, fr, pos, fn, args, argSrc, trace) })

	case *ssa.Go:
        i.wg.Add(1)
        go func() {
            fmt.Fprintf(i.writer, "go routine enter %v\n", fr.String(instr.Call.Func))
            fn, args, argSrc := prepareCall(fr, &instr.Call)
            call(fr.i, nil, instr.Pos(), fn, args, argSrc, true)
            i.wg.Done()
        } ()

	case *ssa.MakeChan:
		fr.env[instr] = make(chan value, asInt(fr.get(instr.Size)))
        if trace {
            fmt.Printf("<<%v = %v %v>>\n", fr.makeVar(instr), "make chan", instr.Type())
        }

	case *ssa.Alloc:
		var addr *value
		if instr.Heap {
			// new
			addr = new(value)
			fr.env[instr] = addr
            if trace {
                fmt.Fprintf(i.writer, "<<%v = heapalloc(%v) [%v]>>\n", fr.makeVar(instr), instr.Type(),fr.env[instr])
            }
		} else {
			// local
			addr = fr.env[instr].(*value)
		}
		*addr = zero(instr.Type().Deref())

	case *ssa.MakeSlice:
		slice := make([]value, asInt(fr.get(instr.Cap)))
		tElt := instr.Type().Underlying().(*types.Slice).Elem()
		for i := range slice {
			slice[i] = zero(tElt)
		}
		fr.env[instr] = slice[:asInt(fr.get(instr.Len))]
        if trace {
            fmt.Fprintf (i.writer, "[%v]\n", instr)
        } 

	case *ssa.MakeMap:
		reserve := 0
		if instr.Reserve != nil {
			reserve = asInt(fr.get(instr.Reserve))
		}
		fr.env[instr] = makeMap(instr.Type().Underlying().(*types.Map).Key(), reserve)
        if trace {
            fmt.Fprintf (i.writer, "<<%v = makeMap %v>>\n", fr.makeVar(instr), instr.Type().Underlying().(*types.Map).Key())
        }

	case *ssa.Range:
		fr.env[instr] = rangeIter(fr.get(instr.X), instr.X.Type())
        if trace {
            fmt.Fprintf (i.writer, "<<%v = %v>>\n", fr.makeVar(instr), instr)
        }

	case *ssa.Next:
		fr.env[instr] = fr.get(instr.Iter).(iter).next()
        if trace {
            fmt.Fprintf (i.writer, "<<%v = %v>>\n", fr.makeVar(instr), instr)
        }

	case *ssa.FieldAddr:
		x := fr.get(instr.X)
		fr.env[instr] = &(*x.(*value)).(structure)[instr.Field]
        name := instr.X.Type().Deref().Underlying().(*types.Struct).Field(instr.Field).Name()
        if trace { // Maybe track alias
            fmt.Fprintf(i.writer, "<<%v = &%v.%v>>\n", fr.makeVar(instr), fr.String(instr.X), name)
        }

	case *ssa.Field:
		fr.env[instr] = copyVal(fr.get(instr.X).(structure)[instr.Field])
        name := instr.X.Type().Deref().Underlying().(*types.Struct).Field(instr.Field).Name()
        if trace { 
            fmt.Fprintf(i.writer, "<<%v = %v.%v>>\n", fr.makeVar(instr), fr.String(instr.X), name)
        }

	case *ssa.IndexAddr:
		x := fr.get(instr.X)
		idx := fr.get(instr.Index)
		switch x := x.(type) {// Maybe track alias
		case []value:
			fr.env[instr] = &x[asInt(idx)]
            if trace {
                fmt.Fprintf(i.writer, "<<%v = &%v[%v]>>\n", fr.makeVar(instr), fr.String(instr.X), instr.Index)
            }
		case *value: // *array
			fr.env[instr] = &(*x).(array)[asInt(idx)]
            if trace {
                fmt.Fprintf(i.writer, "<<%v = &%v[%v]>>\n", fr.makeVar(instr), fr.String(instr.X), instr.Index)
            }
		default:
			panic(fmt.Sprintf("unexpected x type in IndexAddr: %T", x))
		}

	case *ssa.Index:
		fr.env[instr] = copyVal(fr.get(instr.X).(array)[asInt(fr.get(instr.Index))])
        if trace {
            fmt.Fprintf(i.writer, "<<%v = %v[%v]>>\n", fr.makeVar(instr), fr.String(instr.X), instr.Index)
        }

	case *ssa.Lookup:
		fr.env[instr] = lookup(instr, fr.get(instr.X), fr.get(instr.Index))
        if trace {
            fmt.Fprintf(i.writer, "<<%v = %v[%v] [%v]>>\n", fr.makeVar(instr), fr.String(instr.X), fr.String(instr.Index), fr.env[instr])
        }

	case *ssa.MapUpdate:
		m := fr.get(instr.Map)
		key := fr.get(instr.Key)
		v := fr.get(instr.Value)
		switch m := m.(type) {
		case map[value]value:
			m[key] = v
		case *hashmap:
			m.insert(key.(hashable), v)
		default:
			panic(fmt.Sprintf("illegal map type: %T", m))
		}
        if trace {
            fmt.Fprintf (i.writer, "<<%v[%v] = %v [%v]>>\n", fr.String(instr.Map), fr.String(instr.Key), fr.String(instr.Value), v)
        }

	case *ssa.TypeAssert:
		fr.env[instr] = typeAssert(fr.i, instr, fr.get(instr.X).(iface))

	case *ssa.MakeClosure:
		var bindings []value
        var src []string
		for _, binding := range instr.Bindings {
			bindings = append(bindings, fr.get(binding))
            src = append(src, fr.String(binding))
		}
		fr.env[instr] = &closure{instr.Fn.(*ssa.Function), bindings, src}

	case *ssa.Phi:
		for i, pred := range instr.Block().Preds {
			if fr.prevBlock == pred {
				fr.env[instr] = fr.get(instr.Edges[i])
				break
			}
		}

	case *ssa.Select:
		var cases []reflect.SelectCase
		if !instr.Blocking {
			cases = append(cases, reflect.SelectCase{
				Dir: reflect.SelectDefault,
			})
		}
		for _, state := range instr.States {
			var dir reflect.SelectDir
			if state.Dir == ast.RECV {
				dir = reflect.SelectRecv
			} else {
				dir = reflect.SelectSend
			}
			var send reflect.Value
			if state.Send != nil {
				send = reflect.ValueOf(fr.get(state.Send))
			}
			cases = append(cases, reflect.SelectCase{
				Dir:  dir,
				Chan: reflect.ValueOf(fr.get(state.Chan)),
				Send: send,
			})
		}
		chosen, recv, recvOk := reflect.Select(cases)
		if !instr.Blocking {
			chosen-- // default case should have index -1.
		}
		var recvV iface
		if chosen != -1 {
			recvV.t = instr.States[chosen].Chan.Type().Underlying().(*types.Chan).Elem()
			if recvOk {
				// No need to copy since send makes an unaliased copy.
				recvV.v = recv.Interface().(value)
			} else {
				recvV.v = zero(recvV.t)
			}
		}
		fr.env[instr] = tuple{chosen, recvV, recvOk}

	default:
		panic(fmt.Sprintf("unexpected instruction: %T", instr))
	}

	// if val, ok := instr.(ssa.Value); ok {
	// 	fmt.Println(toString(fr.env[val])) // debugging
	// }

	return kNext
}

// prepareCall determines the function value and argument values for a
// function call in a Call, Go or Defer instruction, performing
// interface method lookup if needed.
//
func prepareCall(fr *frame, call *ssa.CallCommon) (fn value, args []value, argSrc []string) {
	if call.Func != nil {
		// Function call.
		fn = fr.get(call.Func)
	} else {
		// Interface method invocation.
		recv := fr.get(call.Recv).(iface)
		if recv.t == nil {
			panic("method invoked on nil interface")
		}
		id := call.MethodId()
		fn = findMethodSet(fr.i, recv.t)[id]
		if fn == nil {
			// Unreachable in well-typed programs.
			panic(fmt.Sprintf("method set for dynamic type %v does not contain %s", recv.t, id))
		}
        argSrc = append(argSrc, fr.String(call.Recv))
		args = append(args, copyVal(recv.v))
	}
	for _, arg := range call.Args {
        argSrc = append(argSrc, fr.String(arg))
		args = append(args, fr.get(arg))
	}
	return
}

// call interprets a call to a function (function, builtin or closure)
// fn with arguments args, returning its result.
// callpos is the position of the callsite.
//
func call(i *interpreter, caller *frame, callpos token.Pos, fn value, args []value, argSrc []string, trace bool) (value, []string) {
	switch fn := fn.(type) {
	case *ssa.Function:
		if fn == nil {
			panic("call of nil function") // nil of func type
		}
        return callSSA(i, caller, callpos, fn, args, nil, argSrc, nil, trace)
	case *closure:
        return  callSSA(i, caller, callpos, fn.Fn, args, fn.Env, argSrc, fn.EnvSrc, trace)
	case *ssa.Builtin:
        return callBuiltin(caller, callpos, fn, args, argSrc)
	}
	panic(fmt.Sprintf("cannot call %T", fn))
}

func loc(fset *token.FileSet, pos token.Pos) string {
	if pos == token.NoPos {
		return ""
	}
	return " at " + fset.Position(pos).String()
}

// callSSA interprets a call to function fn with arguments args,
// and lexical environment env, returning its result.
// callpos is the position of the callsite.
//
func callSSA(i *interpreter, caller *frame, callpos token.Pos, fn *ssa.Function, args []value, env []value, argSrc []string, envSrc []string, trace bool) (value, []string) {
	if i.mode&EnableTracing != 0 {
		fset := fn.Prog.Files
		// TODO(adonovan): fix: loc() lies for external functions.
		fmt.Fprintf(i.writer, "Entering %s%s.\n", fn.FullName(), loc(fset, fn.Pos()))
		suffix := ""
		if caller != nil {
			suffix = ", resuming " + caller.fn.FullName() + loc(fset, callpos)
		}
		defer fmt.Fprintf(i.writer, "Leaving %s%s.\n", fn.FullName(), suffix)
	}
	if fn.Enclosing == nil {
		name := fn.FullName()
		if ext := externals[name]; ext != nil {
			if i.mode&EnableTracing != 0 {
				fmt.Fprintln(i.writer, "\t(external)")
			}
			return ext(fn, args), nil
		}
		if fn.Blocks == nil {
			panic("no code for function: " + name)
		}
	}
    var ptype string
    if caller != nil {
        ptype = caller.packetType
    }
    fcount := atomic.AddUint64(&i.fcount, 1)
	fr := &frame{
		i:      i,
		caller: caller, // currently unused; for unwinding.
		fn:     fn,
		env:    make(map[ssa.Value]value),
		block:  fn.Blocks[0],
		locals: make([]value, len(fn.Locals)),
        labels: make(map[ssa.Instruction] uint64, len(fn.Blocks[0].Instrs)),
        packetType: ptype,
        fvars: make(map[ssa.Value] string),
        fprefix: fmt.Sprintf("f%d", fcount),
        fcount: 0,
	}
	for j, l := range fn.Locals {
		fr.locals[j] = zero(l.Type().Deref())
		fr.env[l] = &fr.locals[j]
        fmt.Fprintf(i.writer, "<<%v = %v>>\n", fr.makeVar(l), fr.locals[j])
	}
	for j, p := range fn.Params {
        fmt.Fprintf(i.writer, "<<%v = %v [%v]>>\n", fr.makeVar(p), argSrc[j], args[j])
		fr.env[p] = args[j]
	}
	for j, fv := range fn.FreeVars {
		fr.env[fv] = env[j]
        fmt.Fprintf(i.writer, "<<%v = %v>>\n", fr.makeVar(fv), env[j])
	}
	var instr ssa.Instruction

	defer func() {
		if fr.status != stComplete {
			if fr.i.mode&DisableRecover != 0 {
				return // let interpreter crash
			}
			fr.status, fr.panic = stPanic, recover()
		}
		fr.rundefers()
		// Destroy the locals to avoid accidental use after return.
		for i := range fn.Locals {
			fr.locals[i] = bad{}
		}
		if fr.status == stPanic {
			panic(fr.panic) // panic stack is not entirely clean
		}
	}()

	for {
		if i.mode&EnableTracing != 0 {
			fmt.Fprintf(i.writer, ".%s:\n", fr.block)
		}
	block:
		for _, instr = range fr.block.Instrs {
			if i.mode&EnableTracing != 0 {
				if v, ok := instr.(ssa.Value); ok {
					fmt.Fprintf(i.writer, "\t%v%s%v %v\n", v.Name(), " = ", instr, reflect.TypeOf(instr))
				} else {
					fmt.Fprintln(i.writer, "\t", instr)
				}
			}
			switch visitInstr(i, fr, instr, trace) {
			case kReturn:
				fr.status = stComplete
				return fr.result, fr.resultSource
			case kNext:
				// no-op
			case kJump:
				break block
			}
		}
	}
	panic("unreachable")
}

// setGlobal sets the value of a system-initialized global variable.
func setGlobal(i *interpreter, pkg *ssa.Package, name string, v value) {
	if g, ok := i.globals[pkg.Var(name)]; ok {
		*g = v
		return
	}
	panic("no global variable: " + pkg.Types.Path() + "." + name)
}

// Interpret interprets the Go program whose main package is mainpkg.
// mode specifies various interpreter options.  filename and args are
// the initial values of os.Args for the target program.
//
// Interpret returns the exit code of the program: 2 for panic (like
// gc does), or the argument to os.Exit for normal termination.
//
func Interpret(mainpkg *ssa.Package, mode Mode, filename string, args []string) (exitCode int) {
	i := &interpreter{
		prog:    mainpkg.Prog,
		globals: make(map[ssa.Value]*value),
		mode:    mode,
        writer:  os.Stdout, 
        gvars: make(map[ssa.Value] string),
        gprefix: "g",
        fcount: 0,
        gcount: 0,
        
	}
	initReflect(i)

	for importPath, pkg := range i.prog.Packages {
		// Initialize global storage.
		for _, m := range pkg.Members {
			switch v := m.(type) {
			case *ssa.Global:
				cell := zero(v.Type().Deref())
				i.globals[v] = &cell
                i.gvars[v] = fmt.Sprintf("%v_%d", i.gprefix, i.fcount)
			}
		}

		// Ad-hoc initialization for magic system variables.
		switch importPath {
		case "syscall":
			var envs []value
			for _, s := range os.Environ() {
				envs = append(envs, s)
			}
			envs = append(envs, "GOSSAINTERP=1")
			setGlobal(i, pkg, "envs", envs)

		case "runtime":
			// TODO(gri): expose go/types.sizeof so we can
			// avoid this fragile magic number;
			// unsafe.Sizeof(memStats) won't work since gc
			// and go/types have different sizeof
			// functions.
			setGlobal(i, pkg, "sizeof_C_MStats", uintptr(3696))

		case "os":
			Args := []value{filename}
			for _, s := range args {
				Args = append(Args, s)
			}
			setGlobal(i, pkg, "Args", Args)
		}
	}

	// Top-level error handler.
	exitCode = 2
	defer func() {
		if exitCode != 2 || i.mode&DisableRecover != 0 {
			return
		}
		switch p := recover().(type) {
		case exitPanic:
			exitCode = int(p)
			return
		case targetPanic:
			fmt.Fprintln(i.writer, "panic:", toString(p.v))
		case runtime.Error:
			fmt.Fprintln(i.writer, "panic:", p.Error())
		case string:
			fmt.Fprintln(i.writer, "panic:", p)
		default:
			fmt.Fprintf(i.writer, "panic: unexpected type: %T\n", p)
		}

		// TODO(adonovan): dump panicking interpreter goroutine?
		// buf := make([]byte, 0x10000)
		// runtime.Stack(buf, false)
		// fmt.Fprintln(i.writer, string(buf))
		// (Or dump panicking target goroutine?)
	}()

	// Run!
	call(i, nil, token.NoPos, mainpkg.Init, nil, nil, false)
	if mainFn := mainpkg.Func("main"); mainFn != nil {
		call(i, nil, token.NoPos, mainFn, nil, nil, false)
        i.wg.Wait()
		exitCode = 0
	} else {
		fmt.Fprintln(i.writer, "No main function.")
		exitCode = 1
	}
	return
}
