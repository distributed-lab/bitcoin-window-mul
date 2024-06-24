import random

def decompose_into_le_naf(k: Integer) -> list[Integer]:
    """
    Decomposes the given integer to its non-adjacent form (NAF) representation.

    Input:
        k (Integer): The integer to be decomposed.
    
    Output:
        list[Integer]: The NAF representation of the given integer.
    """

    decomposition = []
    while k >= 1:
        if k % 2 == 1:
            c = 2 - (k % 4) 
            decomposition.append(c)
            k = k - c
        else:
            decomposition.append(0)
        
        k = k / 2
    
    return decomposition

def mul_naf(k: Integer, n: Integer) -> Integer:
    """
    Multiplies the given integer by the given scalar using the NAF method.

    Input:
        k (Integer): The integer to be multiplied.
        n (Integer): The scalar to multiply the integer by.
    
    Output:
        Integer: The result of the multiplication.
    """

    naf = decompose_into_le_naf(n)
    r = 0

    for _ in range(len(naf)):
        c = naf.pop()
        r = 2 * r
        if c == 1:
            r = r + k
        elif c == -1:
            r = r - k

    return r

a = Integer(random.randint(0, 2**254-1))

# Validating the correctness of the decomposition algorithm
TESTS_NUM = 1000
for _ in range(TESTS_NUM):
    decomposition = decompose_into_le_naf(a)
    assert a == sum([decomposition[i] * 2**i for i in range(len(decomposition))]), 'naf decomposition is incorrect'
    # print(f'The NAF form of integer is: {decomposition}')

# Testing the multiplication algorithm
b = Integer(random.randint(0, 2**254-1))
c = a * b
d = mul_naf(a, b)
assert c == d, 'naf multiplication is incorrect'