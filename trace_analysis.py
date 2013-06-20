import sys
import re
class VarNamer:
    def __init__(self, prefix='t'):
        self.prefix = prefix
        self.count = 0
    def next(self):
        r = "%c%d"%(self.prefix, self.count)
        self.count += 1
        return r
ADDR_PATTERN = r'\&(0x[\d|a-f]*\[[^\s]*\])(.*)$'
PTR_PATTERN = r'\*\((0x[\d|a-f]*\[[^\s]*\])\)(.*)$'
VAR_PATTERN = r'(0x[\d|a-f]*\[[^\s]*\])(.*)$'
OVERALL_PATTERN = r'([^\=]*) \= (.*)$'
VAR_INTERNAL_PATTERN = r'([^\[]*\[[^\]]*\])(.*)$'
CHAN_SEND_PATTERN = r'([^\<]*) \<\- (.*)$'
CHAN_RECV_PATTERN = r'\<\-\(([^\)]*)\)(.*)'
IF_PATTERN = r'if\s*([^\s]*)\s*then\s*([^\s]*)\s*else\s*([^\s]*)(.*)'
def main(args):
    f = open(args[0])
    v = VarNamer()
    vm = {}
    pm = {}
    t  = {}
    def rlookup(lookup, varname):
        rprint = ''
        if lookup.startswith('&'):
            match = re.match(ADDR_PATTERN, lookup)
            varnameR = match.group(1)
            rest = match.group(2)
            varnameR = lookup_var(varnameR)
            pm[varname] = '%s%s'%(varnameR, rest)
            rprint = '&%s'%pm[varname]
        elif lookup.startswith('*'):
            match = re.match(PTR_PATTERN, lookup)
            varnameR = match.group(1)
            rest = match.group(2)
            varnameR = lookup_var(varnameR)
            if varnameR in pm:
                varnameR = pm[varnameR]
                rprint = "%s%s"%(varnameR, rest)
            else:
                rprint = "*%s%s"%(varnameR, rest)
        elif lookup.startswith('0x'):
            match = re.match(VAR_PATTERN, lookup)
            varnameR = match.group(1)
            rest = match.group(2)
            rprint = '%s%s'%(lookup_var(varnameR), rest)
        elif lookup.startswith('<-'):
            match = re.match(CHAN_RECV_PATTERN, lookup)
            varnameR = rlookup(match.group(1), None)
            rest = match.group(2)
            rprint = '<-%s%s'%(varnameR, rest)
        else:
            rprint = parts[1]
        return rprint
    def llookup(lookup):
        lprint = ''
        if lookup.startswith('*'):
            varname = lookup[1:]
            ptr = True
        else:
            ptr = False
            varname = lookup
        varname = lookup_var(varname)
        if ptr and varname in pm: #If we know what the ptr points to, might as well do the right thing
            varname = pm[varname]
            ptr = False
            lprint = varname
        elif ptr:
            lprint = '*%s'%(varname)
        else:
            lprint = varname
        return lprint
    def lookup_var(lookup):
        match = re.match(VAR_INTERNAL_PATTERN, lookup)
        l = match.group(1)
        s = match.group(2)
        if lookup in t:
            varname = t[l]
        else:
            varname = v.next()
            t[l] = varname
        if s.startswith('['):
            s = s.strip()[1:-1]
            translate = rlookup(s, None)
            return '%s[%s]'%(varname, translate)
        else:
            return '%s%s'%(varname, s)
    for l in f:
        if l.startswith('<<'): #ignore non '<<' lines
            l = l.strip()[2:-2]
            if l.startswith('if'): #figure out how to process
                match = re.match(IF_PATTERN, l)
                clause = match.group(1)
                then = match.group(2)
                el = match.group(3)
                rest = match.group(4)
                clause = llookup(clause)
                print 'if %s then %s else %s %s'%(clause, then, el, rest)
            elif '=' in l:
                parts = map(str.strip, list(re.match(OVERALL_PATTERN, l).groups()))
                lprint = llookup(parts[0])
                rprint = rlookup(parts[1], lprint)

                print "%s = %s"%(lprint, rprint)
            elif '<-' in l:
                parts = map(str.strip, list(re.match(CHAN_SEND_PATTERN, l).groups()))
                lprint = llookup(parts[0])
                rprint = rlookup(parts[1], None)
                print "%s <- %s"%(lprint, rprint)
            else:
                print "%s %s"%(l, "Not found")
        else:
            print l.strip()
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print >>sys.stderr, "Too few arguments"
    main(sys.argv[1:])
