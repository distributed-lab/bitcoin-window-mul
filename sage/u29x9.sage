import random

N_BITS = 254
LIMB_SIZE = 29 # 30-bit limbs

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

# Validating the correctness of the conversion
a = Integer(random.randint(0, (1<<N_BITS)-1))
b = Integer(random.randint(0, (1<<N_BITS)-1))
c = a * b

print('a', to_limbs(a))
print('b', to_limbs(b))
print('c', to_limbs(c))
