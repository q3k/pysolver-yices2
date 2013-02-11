import pysolver

# Encrypts dw1 and dw2 (32 bits) with the constant key 0x63737265
def encrypt(dw1, dw2):
    sum = 0
    for i in range(32):
        dw1 += (sum + 0x63737265) ^ (dw2 + ((dw2 << 4) ^ (dw2 >> 5)))
        sum -= 0x61C88647
        dw2 += (sum + 0x63737265) ^ (dw1 + ((dw1 << 4) ^ (dw1 >> 5)))
    return dw1, dw2

if __name__ == '__main__':
    problem = pysolver.Problem()
    dw1 = dw1_in = pysolver.Int(problem, 32)
    dw2 = dw2_in = pysolver.Int(problem, 32)

    dw1, dw2 = encrypt(dw1, dw2)

    dw1.must_be(0x131af1be)
    dw2.must_be(0x4bb34049)
    problem.solve()
    print(hex(dw1_in.model), hex(dw2_in.model))
