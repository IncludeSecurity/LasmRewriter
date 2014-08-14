"""
LasmRewriter.py - Simple script to rewrite LASM output into something more readable
Pull requests are welcome, please find this tool hosted on http://github.com/IncludeSecurity

The MIT License (MIT)

Copyright (c) 2014 Nicolas Rodriguez 
Copyright (c) 2014 Include Security <info [at sign] includesecurity.com>

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

from __future__ import unicode_literals
from collections import defaultdict
from functools import wraps

def ignore_errors(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        try:
            return fn(*args, **kwargs)
        except:
            pass
    return wrapper

class Context:
    PC = 0

    def __init__(self, parent=None):
        self.consts = []
        self.parent = parent
        self.globals = defaultdict(lambda : None)
        self.upvals = defaultdict(lambda : None)
        self.regs = defaultdict(lambda : None)
        self.labels = defaultdict(lambda : None)
        self.child_contexts = []
        self.regs[0] = defaultdict(lambda : None)
        self.upvals[0] = defaultdict(lambda : None) # _ENV
        self.code = []
        self.closure = 1

        # context name
        if parent is None:
            self.parent = self
            self.name = "main"
            self.level = 0
        else:
            self.name = "{}_{}".format(self.parent.name, self.closure)
            self.level = self.parent.level + 1

        self.closure += 1

    def append_context(self, context):
        context.level = self.level + 1
        self.child_contexts.append(context)

    def _to_type(self, v):
        if v.find("\"") != -1:
            return v.replace("\"", "")
        return int(v)

    def RETVALS(self, a, b):
        if int(b) == 1:
            return "regs[{}]".format(a)
        if int(b) == 2:
            return ""
        return " --".join([
            ", ".join(["regs[{}]".format(x) for x in range(int(a), int(b) - 1)]),
            ", ".join([self.regs[x] for x in range(int(a), int(b) - 1)])])

    def RK(self, v):
        if int(v) > 255:
            idx = int(v) - 256
            return self.consts[idx]
        return self.regs[v]

    def mark_label(self, inc_pc=1):
        newpc = self.PC + inc_pc + 1
        label = "lbl_{}".format(newpc)
        self.labels[newpc] = label
        return label

    def next_inst(self):
        self.PC += 1
        label = self.labels.get(self.PC, None)

        if label != None:
            self.code.append("{}:".format(label))

    def get_indent(self, level=0):
        indent = " " * ((self.level - level) * 4)

        if len(indent) == 1:
            return ""
        else:
            return indent

    def get_code(self):
        args = "..." if self.has_vararg else ", ".join([str(x) for x in range(self.no_args)])
        header = "{}function {}({})\n".format(self.get_indent(1), self.name, args)
        body = "\n".join(["{}{}".format(self.get_indent(), x) for x in self.code])
        return "{}{}".format(header, body)

    def get_parent_name(self):
        return "init" if (self.parent is None) else self.parent.name

    def _options(self, no_upvalues, no_args, has_vararg, max_stack):
        self.no_upvalues = int(no_upvalues)
        self.no_args = int(no_args)
        self.has_vararg = (has_vararg == "1")
        self.max_stack = int(max_stack)

    def _const(self, name, *args, **kwargs):
        self.consts.append(self._to_type(name))

    def _name(self, name, *args, **kwargs):
        if len(name.replace("\"", "").strip()) > 0:
            self.name = name

    def _upval(self, name, a, b, *args, **kwargs):
        self.code.append(";; upvals[{}] = {}".format(b, self._to_type(a)))
        self.upvals[b] = self._to_type(a)

    def _loadk(self, a, bx, *args, **kwargs):
        data = self.consts[self._to_type(bx)]
        self.code.append(";; regs[{}] = {}".format(a, repr(data)))
        self.regs[a] = data

    @ignore_errors
    def _add(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = regs[{}] + regs[{}]     ; {} + {}".format(a, b, c, self.RK(b), self.RK(c)))
        self.regs[a] = self.RK(b) + self.RK(c)

    @ignore_errors
    def _sub(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = regs[{}] - regs[{}]     ; {} + {}".format(a, b, c, self.RK(b), self.RK(c)))
        self.regs[a] = self.RK(b) - self.RK(c)

    @ignore_errors
    def _mul(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = regs[{}] * regs[{}]     ; {} + {}".format(a, b, c, self.RK(b), self.RK(c)))
        self.regs[a] = self.RK(b) * self.RK(c)

    @ignore_errors
    def _div(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = regs[{}] / regs[{}]     ; {} + {}".format(a, b, c, self.RK(b), self.RK(c)))
        self.regs[a] = self.RK(b) / self.RK(c)

    @ignore_errors
    def _mod(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = regs[{}] %% regs[{}]     ; {} + {}".format(a, b, c, self.RK(b), self.RK(c)))
        self.regs[a] = self.RK(b) - self.RK(c)

    @ignore_errors
    def _pow(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = regs[{}] ** regs[{}]     ; {} + {}".format(a, b, c, self.RK(b), self.RK(c)))
        self.regs[a] = self.RK(b) ^ self.RK(c)

    @ignore_errors
    def _unm(self, a, b, *args, **kwargs):
        self.code.append("regs[{}] = -regs[{}]    ; -{}".format(a, b, self.RK(b)))
        self.regs[a] = -self.RK(b)

    @ignore_errors
    def _not(self, a, b, *args, **kwargs):
        self.code.append("regs[{}] = not regs[{}]  ; not {}".format(a, b, self.RK(b)))
        self.regs[a] = True if self.RK(b) != 0 else False

    @ignore_errors
    def _length(self, a, b, *args, **kwargs):
        self.code.append("regs[{}] = length(regs[{}])".format(a, self.RK(b)))
        self.regs[a] = len(self.RK(b))

    @ignore_errors
    def _gettabup(self, a, b, c, *args, **kwargs):
        data = self.RK(c)
        self.code.append(";; regs[{0}] = {3}".format(a, b, c, data))
        self.regs[a] = data

    @ignore_errors
    def _gettable(self, a, b, c, *args, **kwargs):
        data = self.RK(c)
        self.code.append(";; regs[{0}] = {1}.{2}".format(a, self.regs[b], data))
        self.regs[a] = "{}.{}".format(self.regs[b], data)

    @ignore_errors
    def _settable(self, a, b, c, *args, **kwargs):
        idx = self.RK(b)
        data = self.RK(c)
        self.code.append("regs[{0}][{1}] = {3}".format(a, idx, c, data))
        self.regs[a][idx] = data

    @ignore_errors
    def _settabup(self, a, b, c, *args, **kwargs):
        idx = self.RK(b)
        data = self.RK(c)
        self.code.append(";; upvals[{0}][{1}] = regs[{2}] ; upvals[{0}][{3}] = regs[{4}]".format(a, b, c, idx, data))
        self.upvals[a][idx] = data

    def _setupval(self, a, b, *args, **kwargs):
        self.code.append(";; upvals[{0}] = regs[{1}]  ; upvals[{0}] = {2}".format(b, a, self.regs[a]))
        self.upvals[b] = self.regs[a]

    def _getupval(self, a, b, *args, **kwargs):
        self.code.append(";; regs[{0}] = {2}".format(a, b, self.upvals[b]))
        self.regs[a] = self.upvals[b]

    def _move(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{0}] = {2}".format(a, b, self.regs[b]))
        self.regs[a] = self.regs[b]

    def _newtable(self, a, b, c, *args, **kwargs):
        self.regs[a] = defaultdict(lambda : None)
        self.code.append("regs[{}] = []".format(a))

    def _loadnil(self, a, b, *args, **kwargs):
        for i in range(int(a), int(b)):
            self.regs[i] = None
            self.code.append("regs[{}] = nil".format(i))

    def _return(self, a, b, c, *args, **kwargs):
        self.code.append("return {}".format(self.RETVALS(a, b)))

    def _getglobal(self, a, b, *args, **kwargs):
        self.code.append("regs[{0}] = globals[{1}]  ; regs[{0}] = {2}".format(a, b, self.consts[b]))
        self.regs[a] = self.globals[self.consts[b]]

    def _setglobal(self, a, b, *args, **kwargs):
        self.code.append("globals[{0}] = regs[{1}]  ; globals[{0}] = {2}".format(b, a, self.regs[a]))
        self.globals[self.consts[b]] = self.regs[a]

    @ignore_errors
    def _self(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = {}".format(int(a) + 1, self.regs[b]))
        self.code.append("regs[{}] = {}.{}()".format(a, self.regs[b], self.RK(c)))

        self.regs[str(int(a) + 1)] = self.regs[b]
        self.regs[a] = "{}.{}".format(self.regs[b], self.RK(c))

    def _test(self, a, c, *args, **kwargs):
        label = self.mark_label(1)
        self.code.append("if regs[{}] == {}: goto {}".format(self.regs[a], c, label))

    def _testset(self, a, b, c, *args, **kwargs):
        label = sel.mark_label(1)

        self.code.append("if ({} != {}):".format(self.regs[b], c))
        self.code.append("  regs[{}] = {}".format(a, self.regs[b]))
        self.code.append("else:")
        self.code.append("  goto {]".format(label))

    def _closure(self, a, b, *args, **kwargs):
        name = "{}_{}".format(self.parent.name, int(b) + 1)
        self.code.append(";; regs[{}] = reference to closure {}".format(a, name))
        self.regs[a] = name

    @ignore_errors
    def _loadbool(self, a, b, c, *args, **kwargs):
        self.code.append("regs[{}] = (bool){}".format(a, self.regs[b]))

        if int(c) != 0:
            self.code.append("goto {}".format(self.mark_label(1)))

        self.regs[a] = True if int(b) != 0 else False

    def _tforcall(self, a, c, *args, **kwargs):
        res = ",".join(["regs[{}]".format(x) for x in range(int(a) + 3, int(a) + 3 + int(c))])
        self.code.append("{0} = call function in regs[{1}](regs[{2}], regs[{3}])   ;; {4}".format(res,
            a, int(a) + 1, int(a) + 2, self.regs[a]))

    def _tforloop(self, a, b, *args, **kwargs):
        ar = int(a) + 1
        label = self.mark_label(int(b))
        self.code.append("if regs[{}] != nil then  ; => {}".format(ar, self.regs[ar]))
        self.code.append("    regs[{}] = regs[{}]".format(a, ar))
        self.code.append("    goto {}".format(label))
        self.code.append("end")

    def _setlist(self, a, b, c, *args, **kwargs):
        for i in range(1, b):
            self.code.append("regs[{}][{}] = regs[{}]".format(self.regs[a], i, self.regs[str(int(a) + i)]))

    def _forprep(self, a, b, *args, **kwargs):
        label = self.mark_label(int(b))
        self.code.append("regs[{0}] -= regs[{1}]  ; regs[{0}] -= {2}".format(a, int(a) + 2, self.regs[int(a) + 2]))
        self.code.append("goto {}".format(label))

    def _forloop(self, b, *args, **kwargs):
        label = self.mark_label(int(b))
        self.code.append("regs[{0}] += regs[{1}]  ; regs[{0}] += {2}".format(a, int(a) + 2, self.regs[int(a) + 2]))
        self.code.append("if regs[{0}] <?= regs[{1}] then".format(a, int(a) + 1))
        self.code.append("    regs[{0}] = regs[{1}]   ; regs[{0}] = {2}".format(int(a) + 3, a, self.regs[a]))
        self.code.append("    goto {}".format(label))
        self.code.append("end")

    def _vararg(self, a, b, *args, **kwargs):
        tmp = self.no_args if (int(b) == 0) else int(b) - 1
        regs = ", ".join(["regs[{}]".format(x) for x in range(int(a), tmp)])
        vargs = ", ".join(["args[{}]".format(x) for x in range(int(a), tmp)])
        tmp = " = " if len(regs.strip()) > 0 else ""
        self.code.append("{}{}{}".format(regs, tmp,vargs))

    def _eq(self, a, b, c, *args, **kwargs):
        label = self.mark_label(1)
        self.code.append("if ({} == {}) != {}: goto {}".format(self.RK(b), self.RK(c), a, label))

    def _lt(self, a, b, c, *args, **kwargs):
        label = self.mark_label(1)
        self.code.append("if ({} < {}) == {}: goto {}".format(self.RK(b), self.RK(c), a, label))

    def _le(self, a, b, c, *args, **kwargs):
        label = self.mark_label(1)
        self.code.append("if ({} <= {}) == {}: goto {}".format(self.RK(b), self.RK(c), a, label))

    def _tailcall(self, a, b, c, *args, **kwargs):
        params = ", ".join(["regs[{}]".format(x) for x in range(int(a) + 1, int(a) + int(b) + 1)])
        self.code.append("return regs[{0}]({1}) ; regs[{0}] = {2}".format(a, params, self.regs[a]))

    def _call(self, a, b, c, *args, **kwargs):
        params = ", ".join([str(self.regs[str(x)]) or "" for x in range(int(a) + 1, int(a) + int(b))])
        res = ", ".join(["regs[{}]".format(x) for x in range(int(a), int(a) + int(c) - 1)])
        tmp = " = " if len(res.strip()) > 0 else ""
        self.code.append("{}{}{}({})".format(res, tmp, self.regs[a], params))

    def _concat(self, a, b, c, *args, **kwargs):
        data = []
        for i in range(int(b), int(c) + 1):
            if not self.regs[i] is None:
                data.append(self.regs[i])

        self.code.append("regs[{}] = {}".format(a, " + ".join(data)))
        self.regs[a] = " + ".join(data)

    def _jmp(self, a, b, *args, **kwargs):
        self.code.append("goto {}".format(self.mark_label(int(b))))

        if int(a) != 0:
            for i in range(int(a) + 1, self.no_upvalues):
                self.code.append("upvals[{}] = nil   ; close upvalue!".format(i))

def translate_proc(fh, parent_context=None):
    context = Context(parent_context)

    while True:
        line = fh.readline()
        if not line:
            break

        # skip comments
        line = line.strip()
        if line.startswith(";") or len(line) == 0:
            continue

        context.next_inst()
        parts = line.split()
        inst = "_{}".format(parts[0].replace(".", ""))

        if inst == "_func":
            child = translate_proc(fh, context)
            context.append_context(child)
        elif inst == "_end":
            break
        else:
            if hasattr(context, inst):
                getattr(context, inst)(*parts[1:])
            else:
                context.code.append(" -- Unsupported Instruction: [{}]".format(line))
    return context

def traverse_code(parent):
    print(parent.get_code())

    for child in parent.child_contexts:
        traverse_code(child)

    print("{}end".format(parent.get_indent(1)))

def main():
    import sys
    import os.path

    if len(sys.argv) != 2:
        print("Use: LasmRewriter.py <lasm_file>")
        sys.exit(1)

    filename = sys.argv[1]

    if not os.path.exists(filename):
        print("Error: file {} does not exists!".format(filename))
        sys.exit(2)

    with open(filename, "r") as fh:
        main = translate_proc(fh)

    traverse_code(main)

if __name__ == '__main__':
    main()