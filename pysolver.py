import subprocess
import tempfile

def bits(b, n):
    for i in xrange(b):
        yield (n & 1)
        n >>= 1

class Var:
    def __init__(self, problem, id, negated=False):
        self.problem = problem
        self.id = id
        self.negated = negated

    def __neg__(self):
        return Var(self.problem, self.id, not self.negated)

    def for_clause(self):
        return str(self.id) if not self.negated else "-%d" % self.id

    @property
    def model(self):
        return self.problem.model[self.id]

class Problem:
    def __init__(self):
        self.free_id = 1
        self.clauses = []
        self.model = {}

    def new_var(self):
        id = self.free_id
        self.free_id += 1
        return Var(self, id)

    def add_or(self, *vars):
        c = ' '.join(v.for_clause() for v in vars) + " 0"
        self.clauses.append(c)

    def dimacs(self):
        s = 'p cnf %d %d\n' % (self.free_id - 1, len(self.clauses))
        return s + '\n'.join(self.clauses)

    def solve(self):
        f = tempfile.NamedTemporaryFile(delete=False)
        name = f.name
        f.write(self.dimacs())
        f.close()
        proc = subprocess.Popen(["yices-sat", "-m", name], stdin=subprocess.PIPE,
                stdout=subprocess.PIPE)
        stdout, stderr = proc.communicate()
        lines = stdout.decode('utf-8').split('\n')
        if lines[0] != 'sat':
            raise RuntimeError("UNSAT")

        vals = lines[1].split()
        for val in vals:
            if val.startswith('-'):
                val = (val[1:], False)
            else:
                val = (val, True)
            self.model[int(val[0])] = val[1]

class Int:
    def __init__(self, problem, size, bits=None, val=None):
        self.problem = problem
        if bits is None:
            self.bits = [problem.new_var() for b in range(size)]
        else:
            self.bits = bits
        self.size = size
        if val is not None:
            self.must_be(val)

    def must_be(self, cst):
        for i in range(self.size):
            b = cst & 1
            cst >>= 1
            self.problem.add_or(self.bits[i] if b else -self.bits[i])

    def _convert_for_op(self, cst):
        if isinstance(cst, Int):
            if cst.size != self.size:
                raise ValueError("not the same size")
            return cst
        return Int(self.problem, self.size, val=cst)

    def __add__(self, other):
        other = self._convert_for_op(other)

        def bitadder(a, b, c):
            res = self.problem.new_var()
            res_carry = self.problem.new_var()

            self.problem.add_or(res_carry, a, -b, -c)
            self.problem.add_or(res_carry, -a, b, -c)
            self.problem.add_or(res_carry, -a, -b, c)
            self.problem.add_or(res_carry, -a, -b, -c)
            self.problem.add_or(-res_carry, a, b, c)
            self.problem.add_or(-res_carry, a, b, -c)
            self.problem.add_or(-res_carry, a, -b, c)
            self.problem.add_or(-res_carry, -a, b, c)

            self.problem.add_or(res, a, b, -c)
            self.problem.add_or(res, a, -b, c)
            self.problem.add_or(res, -a, b, c)
            self.problem.add_or(res, -a, -b, -c)
            self.problem.add_or(-res, a, b, c)
            self.problem.add_or(-res, a, -b, -c)
            self.problem.add_or(-res, -a, b, -c)
            self.problem.add_or(-res, -a, -b, c)

            return res, res_carry

        carry = self.problem.new_var()
        self.problem.add_or(-carry)

        bits = []
        for a, b in zip(self.bits, other.bits):
            res, carry = bitadder(a, b, carry)
            bits.append(res)
        return Int(self.problem, self.size, bits=bits)

    def __and__(self, other):
        other = self._convert_for_op(other)
        ret = Int(self.problem, self.size)

        bits = []
        for a, b in zip(self.bits, other.bits):
            c = self.problem.new_var()
            self.problem.add_or(-c, a)
            self.problem.add_or(-c, b)
            self.problem.add_or(c, -a, -b)
            bits.append(c)
        return Int(self.problem, self.size, bits=bits)

    def __invert__(self):
        bits = [self.problem.new_var() for i in range(self.size)]
        for (b, i) in zip(self.bits, bits):
            self.problem.add_or(b, i)
            self.problem.add_or(-b, -i)
        return Int(self.problem, self.size, bits=bits)

    def __lshift__(self, other):
        if isinstance(other, Int):
            raise TypeError("variable bit shift not implemented")
        other = min(other, self.size)
        if other == 0:
            return self
        zero_bits = Int(self.problem, other, val=0).bits
        bits = zero_bits + self.bits[:-other]
        return Int(self.problem, self.size, bits=bits)

    def __neg__(self):
        return ~self + 1

    def __or__(self, other):
        other = self._convert_for_op(other)
        ret = Int(self.problem, self.size)

        bits = []
        for a, b in zip(self.bits, other.bits):
            c = self.problem.new_var()
            self.problem.add_or(c, -a)
            self.problem.add_or(c, -b)
            self.problem.add_or(-c, a, b)
            bits.append(c)
        return Int(self.problem, self.size, bits=bits)

    def __rshift__(self, other):
        if isinstance(other, Int):
            raise TypeError("variable bit shift not implemented")
        other = min(other, self.size)
        zero_bits = Int(self.problem, other, val=0).bits
        bits = self.bits[other:] + zero_bits
        return Int(self.problem, self.size, bits=bits)

    def __xor__(self, other):
        other = self._convert_for_op(other)
        bits = [self.problem.new_var() for i in range(self.size)]
        for (a, b, o) in zip(self.bits, other.bits, bits):
            self.problem.add_or(o, a, -b)
            self.problem.add_or(o, -a, b)
            self.problem.add_or(-o, a, b)
            self.problem.add_or(-o, -a, -b)
        return Int(self.problem, self.size, bits=bits)

    def __rxor__(self, other):
        return self ^ other

    @property
    def model(self):
        n = 0
        for i, v in enumerate(self.bits):
            n |= int(v.model) << i
        return n

class Mapping:
    def __init__(self, problem, valbits, vals):
        self.problem = problem
        self.valbits = valbits
        self.vals = vals

    def __getitem__(self, inp):
        ret = Int(self.problem, self.valbits)

        for k, v in enumerate(self.vals):
            # (inp = k) => (ret = v) with k and v consts
            const_part = [-inp.bits[i] if b else inp.bits[i]
                          for i, b in enumerate(bits(self.valbits, k))]
            for b, val_b in zip(ret.bits, bits(self.valbits, v)):
                self.problem.add_or(b if val_b else -b, *const_part)

        return ret
