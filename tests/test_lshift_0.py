import os
import sys
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

import pysolver

if __name__ == '__main__':
    problem = pysolver.Problem()

    dw1 = dw1_ = pysolver.Int(problem, 8)

    dw1 = dw1 << 0

    dw1.must_be(0x42)
    problem.solve()
    print(hex(dw1_.model))
