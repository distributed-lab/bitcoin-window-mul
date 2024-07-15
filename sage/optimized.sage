import random

def to_window_w_form(n: Integer, w: Integer) -> Integer:
    """
    Converts the given integer n into the w-width representation
    """

    decomposition = []
    while n >= 1:
        c = n % (1 << w)
        decomposition.append(c)
        n = n - c
        n = n // (1 << w)
    
    return decomposition

def mul_window_w_form(x: Integer, y: Integer, w: Integer) -> Integer:
    """
    Multiplies two integers using window-w form
    """

    d = to_window_w_form(y, w)
    if len(d) == 63: # Ensuring that the decomposition is 64-bit
        d.append(0)
    
    precompute_table = [i*x for i in range(1<<w)]

    r = precompute_table[d[63]]
    print(r.nbits())
    for i in range(1, 64):
        k = 256 + 4*i
        for _ in range(4):
            r = 2*r
        r = r + precompute_table[d[63-i]]
        print(r.nbits())
        assert k == r.nbits()
        
    return r

a = (1<<254)-1 # First random 254-bit integer
b = (1<<254)-1 # Second random 254-bit integer

w = 4 # Window width

# Asserting that the decomposition is correct
b_decomposition = to_window_w_form(b, w)
if len(b_decomposition) == 63:
    b_decomposition.append(0)
assert sum([2**(w*i)*c for i, c in enumerate(b_decomposition)]) == b, 'decomposition is wrong'
print('decomposition is correct')

# Asserting that the multiplication is correct
c = a * b
assert mul_window_w_form(a, b, 4) == c, 'multiplication is wrong'
print('multiplication is correct')