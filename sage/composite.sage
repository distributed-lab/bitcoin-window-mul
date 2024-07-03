import random

N_BITS = 254*2 # Composite bigint from two 254-bit bigints
LIMB_SIZE = 30 # 30-bit limbs

def to_limbs(a: Integer) -> list[Integer]:
    """
    Converts the given integer a into a list of 254-bit limbs
    """
    limbs = []
    while a >= 1:
        c = a % (1 << LIMB_SIZE)
        limbs.append(c)
        a = a - c
        a = a // (1 << LIMB_SIZE)
    
    return limbs

def equal_limbs(a: list[Integer], b: list[Integer]) -> bool:
    """
    Compares two lists of limbs
    """
    if len(a) != len(b):
        return False

    for i in range(len(a)):
        if a[i] != b[i]:
            return False

    return True

# Validating the correctness of the conversion
a = Integer('0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47')
assert equal_limbs(to_limbs(a), [
    410844487,
    813838427,
    119318739,
    542811226,
    22568343,
    18274822,
    436378501,
    329037900,
    12388
]), f'conversion is wrong, got: {to_limbs(a)}'

a = Integer(random.randint(0, (1<<N_BITS)-1))
print(f'a = {a}')
print(f'hex(a) = {a.hex()}')
print(f'limbs = {to_limbs(a)}')
print(f'# of limbs = {len(to_limbs(a))}')