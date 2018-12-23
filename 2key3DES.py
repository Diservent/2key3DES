import functools
import struct
import math
import random
import textwrap
import os

_isprime_fallback_primes = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
    109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
    173, 179, 181, 191, 193, 197, 199]

_pseudos = set([
            669094855201,
           1052516956501,2007193456621,2744715551581,9542968210729,
          17699592963781,19671510288601,
          24983920772821,24984938689453,29661584268781,37473222618541,
          46856248255981,47922612926653,48103703944453,49110566041153,
          49752242681221,91206655032481,91481980096033,119034193492321,
         123645258399601,128928036060253,137364148720147,150753857310253,
         153131886327421,155216912613121,185610214763821,224334357392701,
         227752294950181,230058334559041,304562854940401,306001576998253,
         335788261073821,377133492079081,379242177424951,389970770948461,
         397319638319521,448114903362253,523235160050221,628999496281621,
         699349238838253,746667678235753,790198268451301,794036495175661,
         823820871230281,867739535711821,1039918661294761,1099127938585141,
        1104388025338153,1173374598605653,1262797719066157,1265872947674653,
        1325898212229667,1327034517143653,1418575746675583,1666122072463621,
        1837400535259453,1857422490084961,1870756820971741,1914550540480717,
        2018963273468221,2163829000939453,2206020317369221,2301037384029121,
        2416062055125421,2435076500074921,2545656135020833,2594428516569781,
        2669983768115821,2690937050990653,2758640869506607,2833525461416653,
        2876662942007221,2932155806957821,2957010595723801,3183606449929153,
        3220133449185901,3424103775720253,3625360152399541,3939300299037421,
        3947917710714841,3980273496750253,4182256679324041,4450605887818261,
        4727893739521501,4750350311306953,4755334362931153,5756440863559753,
        5760976603475341,5794399356078761,5954850603819253,6125544931991761,
        6320931714094861,6347593619672581,6406268028524101,6510632945054941,
        6620082224794741,6627325072566061,6844056606431101,6989404981060153,
        7144293947609521,7288348593229021,7288539837129253,7406102904971689,
        7430233301822341,7576425305871193,7601696719033861,7803926845356487,
        7892007967006633,7947797946559453,8207000460596953,8295064717807513,
        8337196000698841,8352714234009421,8389755717406381,8509654470665701,
        8757647355282841,8903933671696381,8996133652295653,9074421465661261,
        9157536631454221,9188353522314541])

IP = [
  58, 50, 42, 34, 26, 18, 10, 2,
  60, 52, 44, 36, 28, 20, 12, 4,
  62, 54, 46, 38, 30, 22, 14, 6,
  64, 56, 48, 40, 32, 24, 16, 8,
  57, 49, 41, 33, 25, 17,  9 ,1,
  59, 51, 43, 35, 27, 19, 11, 3,
  61, 53, 45, 37, 29, 21, 13, 5,
  63, 55, 47, 39, 31, 23, 15, 7,
]

IP_INV = [
  40,  8, 48, 16, 56, 24, 64, 32,
  39,  7, 47, 15, 55, 23, 63, 31,
  38,  6, 46, 14, 54, 22, 62, 30,
  37,  5, 45, 13, 53, 21, 61, 29,
  36,  4, 44, 12, 52, 20, 60, 28,
  35,  3, 43, 11, 51, 19, 59, 27,
  34,  2, 42, 10, 50, 18, 58, 26,
  33,  1, 41,  9, 49, 17, 57,25,
]

E = [
  32,  1,  2,  3,  4,  5,
   4,  5,  6,  7,  8,  9,
   8,  9, 10, 11, 12, 13,
  12, 13, 14, 15, 16, 17,
  16, 17, 18, 19, 20, 21,
  20, 21, 22, 23, 24, 25,
  24, 25, 26, 27, 28, 29,
  28, 29, 30, 31, 32,  1,
]

PC1_C = [
  57, 49, 41, 33, 25, 17,  9,
   1, 58, 50, 42, 34, 26, 18,
  10,  2, 59, 51, 43, 35, 27,
  19, 11,  3, 60, 52, 44, 36,
]

PC1_D = [
  63, 55, 47, 39, 31, 23, 15,
   7, 62, 54, 46, 38, 30, 22,
  14,  6, 61, 53, 45, 37, 29,
  21, 13,  5, 28, 20, 12,  4,
]

PC2 = [
  14, 17, 11, 24,  1, 5,
   3, 28, 15,  6, 21, 10,
  23, 19, 12,  4, 26, 8,
  16,  7, 27, 20, 13, 2,
  41, 52, 31, 37, 47, 55,
  30, 40, 51, 45, 33, 48,
  44, 49, 39, 56, 34, 53,
  46, 42, 50, 36, 29, 32,
]

KS_SHIFTS = [1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1]

S1 = [
  [14,  4, 13, 1,  2, 15, 11,  8,  3, 10,  6, 12,  5,  9, 0,  7],
  [ 0, 15,  7, 4, 14,  2, 13,  1, 10,  6, 12, 11,  9,  5, 3,  8],
  [ 4,  1, 14, 8, 13,  6,  2, 11, 15, 12,  9,  7,  3, 10, 5,  0],
  [15, 12,  8, 2,  4,  9,  1,  7,  5, 11,  3, 14, 10,  0, 6, 13],
]

S2 = [
  [15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10],
  [3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5],
  [0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15],
  [13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9],
]

S3 = [
  [10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8],
  [13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1],
  [13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7],
  [1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12],
]

S4 = [
  [7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15],
  [13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9],
  [10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4],
  [3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14],
]

S5 = [
  [2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9],
  [14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6],
  [4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14],
  [11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3],
]

S6 = [
  [12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11],
  [10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8],
  [9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6],
  [4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13],
]

S7 = [
  [4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1],
  [13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6],
  [1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2],
  [6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12],
]

S8 = [
  [13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7],
  [1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2],
  [7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8],
  [2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11],
]


SBOXES = [S1,S2,S3,S4,S5,S6,S7,S8]

P = [
  16,  7, 20, 21,
  29, 12, 28, 17,
   1, 15, 23, 26,
   5, 18, 31, 10,
   2,  8, 24, 14,
  32, 27,  3,  9,
  19, 13, 30,  6,
  22, 11,  4, 25,
]
################################################Проверка на простоту и генератор ключей#################################################
def _test(n, base):
    from sympy.ntheory.factor_ import trailing
    n = int(n)
    if n < 2:
        return False
    # remove powers of 2 from n (= t * 2**s)
    s = trailing(n - 1) # Count the number of trailing zero digits in the binary representation of n,
                        # i.e. determine the largest power of 2 that divides n
    t = n >> s
    # test Ferma
    b = pow(base, t, n)
    if b == 1 or b == n-1:
        return True
    else:
        for j in range(1, s):
            b = (b**2) % n
            if b == n-1:
                return True
    return False

def mr(n, bases):
    n = int(n)
    for base in bases:
        if not _test(n, base):
            return False
    return True

def _mr_safe(n):
    if n < 1373653:
        return mr(n, [2, 3])
    if n < 170584961:
        return mr(n, [350, 3958281543])
    if n < 4759123141:
        return mr(n, [2, 7, 61])
    if n < 75792980677:
        return mr(n, [2, 379215, 457083754])
    if n < 1000000000000:
        return mr(n, [2, 13, 23, 1662803])
    if n < 10000000000000000:
        return mr(n, [2, 3, 7, 61, 24251]) and n not in _pseudos
    raise ValueError("n too large")

def isprime(n): ##
    n = int(n)
    if n < 2:
        return False
    if n & 1 == 0:
        return n == 2
    if n <= 23001:
        return pow(2, n, n) == 2 and n not in [341, 561, 645, 1105, 1387, 1729,
                                               1905, 2047, 2465, 2701, 2821,
                                               3277, 4033, 4369, 4371, 4681,
                                               5461, 6601, 7957, 8321, 8481,
                                               8911, 10261, 10585, 11305,
                                               12801, 13741, 13747, 13981,
                                               14491, 15709, 15841, 16705,
                                               18705, 18721, 19951, 23001]
    try:
        return _mr_safe(n)
    except ValueError:
        return mr(n, _isprime_fallback_primes)


#Ген ключей
def prime_num_gen1(num_of_bytes):
    a = os.urandom(num_of_bytes)
    key_int = int.from_bytes(a, byteorder='big')
    while isprime(key_int)==False:
        key_int+=1
    return key_int
#####################################################################################################################################

#######################Основные функции DES#################################################################
def xor(b1, b2):
  """Xors two bit vectors together."""
  return [x ^ y for x, y in zip(b1, b2)]

def Concat(*vectors):
  """Concats vectors."""
  return functools.reduce(lambda x, y: x + y, vectors, [])

def Expand(v):
  """Expands 32bits into 48 bits."""
  assert (len(v) == 32)
  return [v[E[i] - 1] for i in range(48)]

# t=1
def LeftShift(v, t):   
  """Left shitfs (rotates) a vector of bits t times."""
  return v[t:] + v[:t]

def KeyScheduler(key):
  """Yields round keys."""
  assert (len(key) == 64)
  # Only 56 bits are used. A bit in each byte is reserved for pairity checks.
  C = [key[PC1_C[i] - 1] for i in range(28)]
  D = [key[PC1_D[i] - 1] for i in range(28)]

  for ri in range(16):
    C = LeftShift(C, KS_SHIFTS[ri])
    D = LeftShift(D, KS_SHIFTS[ri])

    CD = Concat(C, D)
    ki = [CD[PC2[i] - 1] for i in range(48)]
    yield ki


def CipherFunction(key, inp):
  """Single confusion-diffusion step."""
  assert (len(key) == 48)
  assert (len(inp) == 32)

  # Confusion step.
  res = xor(Expand(inp), key)
  sbox_out = []
  for si in range(48 // 6):
    sbox_inp = res[6 * si:6 * si + 6]
    sbox = SBOXES[si]
    row = (int(sbox_inp[0]) << 1) + int(sbox_inp[-1])
    col = int(''.join([str(b) for b in sbox_inp[1:5]]), 2)
    bits = bin(sbox[row][col])[2:]
    bits = '0' * (4 - len(bits)) + bits
    sbox_out += [int(b) for b in bits]
    # Diffusion step.
  res = sbox_out
  res = [res[P[i] - 1] for i in range(32)]
  return res


def DESEncrypt(plaintext, key):
  # Initial permutation.
  plaintext = [plaintext[IP[i] - 1] for i in range(64)]
  L, R = plaintext[:32], plaintext[32:]

  # Feistel network.
  for ki in KeyScheduler(key):
    L, R = R, xor(L, CipherFunction(ki, R))

  # Final permutation.
  ciphertext = Concat(R, L)
  ciphertext = [ciphertext[IP_INV[i] - 1] for i in range(64)]

  return ciphertext


def DESDecrypt(ciphertext, key):
  # Initial permutation.
  ciphertext = [ciphertext[IP[i] - 1] for i in range(64)]
  L, R = ciphertext[:32], ciphertext[32:]

  # Feistel network.
  for ki in reversed(list(KeyScheduler(key))):
    L, R = R, xor(L, CipherFunction(ki, R))

  # Final permutation.
  plaintext = Concat(R, L)
  plaintext = [plaintext[IP_INV[i] - 1] for i in range(64)]

  return plaintext



############################################################



key1=prime_num_gen1(8)
key2=prime_num_gen1(8)
print("\nKey1 = ",key1)
print("\nKey2 = ",key2)
bin_key1=bin(key1)[2:]
while len(bin_key1)%64!=0: 
	bin_key1='0'+bin_key1 
key1 = [int(i) for i in bin_key1] 
bin_key2=bin(key2)[2:]
while len(bin_key2)%64!=0: 
	bin_key2='0'+bin_key2 
key2 = [int(i) for i in bin_key2]


##########################


# открываем файл, переводим в лист битов
f = open('test.txt')
for line in f:
    stin =line
bi=' '.join(format(ord(x), 'b') for x in stin)
bi=bi.split(' ')
i=0
for x in bi:

    while (len(bi[i]) < 11):
        bi[i]='0'+ bi[i]
    i+=1
bi=''.join(bi)
while (len(bi)%64!=0):
    bi+='0'
bi = [int(i) for i in bi] 
final = []
cipher=[]
# получаем лист битов

#                     Шифрование 2 ключами 3DES
for z in range(len(bi) // 64):
	encrypt1 = DESEncrypt(bi[64*z:64*z+64], key1)
	decrypt2 = DESDecrypt(encrypt1, key2)
	encrypt3 = DESEncrypt(decrypt2, key1)
	cipher = Concat(cipher,encrypt3)

# перевод битов в текст
bit_text = ''.join(str(x) for x in cipher)
bit_text=''.join(bit_text)
bit_text=textwrap.wrap(bit_text, 11)
if(len(bit_text[len(bit_text)-1]) < 11):
    del bit_text[len(bit_text)-1]
crypt=''.join(chr(int(x,2)) for x in bit_text)
print("\nEncrypted:",crypt)
# ################################                      Результат шифрования 2 ключами 3DES

#           расшифровка DED
for z in range(len(cipher) // 64):
	decrypt4 = DESDecrypt(cipher[64*z:64*z+64], key1)
	encrypt5 = DESEncrypt(decrypt4, key2)
	decrypt6 = DESDecrypt(encrypt5, key1)
	final = Concat(final,decrypt6)

#         перевод битов в текст
bit_text = ''.join(str(x) for x in final)
bit_text=''.join(bit_text)
bit_text=textwrap.wrap(bit_text, 11)
if(len(bit_text[len(bit_text)-1]) < 11):
    del bit_text[len(bit_text)-1]
opentext=''.join(chr(int(x,2)) for x in bit_text)
print("\nDecrypted:",opentext)

