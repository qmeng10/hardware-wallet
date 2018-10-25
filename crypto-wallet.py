#!/usr/bin/env python
""" crypto-wallet.py

    A library of routines to find prime numbers.
    
    When run from the commandline it randomly generates and displays a prime
    number of the size provided by the 'size' argument.
    
    References:
      HAC - "Handbook of Applied Cryptography",Menezes, van Oorschot, Vanstone; 1996
      https://inventwithpython.com/rabinMiller.py 
      http://rosettacode.org/wiki
"""
RABIN_MILLER_ITERATIONS = 40
SIZE = 5
from os import urandom
import random

def fermat_little_test( p, a ):
    """ Fermat Little Test. Included as a curiosity only.
        p - possible Prime,
        a - any integer
        
        Fermat's Liitle test says that non-primes always have the property that:
        a**(p-1) == 0  mod(p)
    """
    if pow(a,p-1,p) == 1 :
        return True  # could be prime
    else:
        return False  # is NOT prime

def rabin_miller(possiblePrime, aTestInteger):
    """ The Rabin-Miller algorithm to test possible primes
        taken from HAC algorithm 4.24, without the 't' loop
    """
    # if ( 1<= aTestInteger <= (possiblePrime-1) ):
    #     print('test integer %d out of range for %d'%(aTestInteger,possiblePrime))
    #     return


    # if ( possiblePrime % 2 == 1 ): 
    #     print('possiblePrime must be odd')
    #     return

    # calculate s and r such that (possiblePrime-1) = (2**s)*r  with r odd
    r = possiblePrime-1
    s=0
    while (r%2)==0 :
        s+=1
        r=int(r/2)
    y = pow(aTestInteger,r,possiblePrime)
    if ( y!=1 and y!=(possiblePrime-1) ) :
        j = 1
        while ( j <= s-1 and y!=possiblePrime-1 ):
            y = pow(y,2,possiblePrime) #    (y*y) % n
            if y==1 :
                return False # failed - composite
            j = j+1
        if y != (possiblePrime-1):
            return False # failed - composite
    return True          # success, still a possible prime


def is_prime(possible_prime, verbose=False):
    """ Test a number for primality using Rabin-Miller. 
    """
    # prescreen the possible_prime for divisibility by low primes
    for prime in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
                  47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
                  103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
                  157, 163, 167, 173, 179, 181, 191, 193, 197, 199,
                  211, 223, 227, 229, 233, 239, 241, 251, 257):
        if possible_prime % prime == 0:
            if possible_prime == prime:
                return True # for small primes need to check equality
            else:
                if verbose: print("Failed division by: {}".format(prime))
                return False # divisible by small prime from list
                  
    # each successful iteratation 't', the probability of
    # the number being prime increases:  prob = (1-(1/4)**t)
    for iteration in range( RABIN_MILLER_ITERATIONS ):
        witness = random.randrange(2, possible_prime - 1)
        if not rabin_miller(possible_prime, witness):
            if verbose: print("Failed Rabin-Miller iteration: {}".format(iteration))
            return False

    return True


def int_to_string( long_int, padto=None ):
    """ Convert integer long_int into a string of bytes, as per X9.62.
        If 'padto' defined, result is zero padded to this length.
        """
    if long_int > 0:
        octet_string = ""
        while long_int > 0:
            long_int, r = divmod( long_int, 256 )
            octet_string = chr( r ) + octet_string
    elif long_int == 0:
        octet_string = chr(0)
    else:
        raise ValueError('int_to-string unable to convert negative numbers')
    
    if padto:
        padlen = padto - len(octet_string)
        assert padlen >= 0
        octet_string = padlen*chr(0) + octet_string
    return octet_string

def string_to_int( octet_string ):
    """ Convert a string of bytes into an integer, as per X9.62. """
    long_int = 0
    for c in octet_string:
        long_int = 256 * long_int + c
    return long_int

def new_random_prime(size_in_bytes, debug=False):
    """ Finds a prime number of close to a specific integer size.
    """
    possible_prime = string_to_int( urandom(size_in_bytes) )
    if not possible_prime % 2:  # even, +1 to make odd
        possible_prime += 1
    
    count = 0
    while True:
        count += 1
        if is_prime( possible_prime, verbose=debug ):
            if debug: print("Prime found after {} attempts.".format(count))
            break
        else:
            possible_prime += 2

    return possible_prime

'''
The keys for the RSA algorithm are generated the following way:

    Choose two distinct prime numbers p and q.
        For security purposes, the integers p and q should be chosen at random, and should be similar in magnitude but differ in length by a few digits to make factoring harder.[2] Prime integers can be efficiently found using a primality test.
    Compute n = pq.
        n is used as the modulus for both the public and private keys. Its length, usually expressed in bits, is the key length.
    Compute λ(n) = lcm(λ(p), λ(q)) = lcm(p − 1, q − 1), where λ is Carmichael's totient function. This value is kept private.
    Choose an integer e such that 1 < e < λ(n) and gcd(e, λ(n)) = 1; i.e., e and λ(n) are coprime.
    Determine d as d ≡ e−1 (mod λ(n)); i.e., d is the modular multiplicative inverse of e (modulo λ(n)).

            This means: solve for d the equation d⋅e ≡ 1 (mod λ(n)).
            e having a short bit-length and small Hamming weight results in more efficient encryption – most commonly e = 216 + 1 = 65,537. However, much smaller values of e (such as 3) have been shown to be less secure in some settings.[14]
            e is released as the public key exponent.
            d is kept as the private key exponent.

    From wiki
'''

'''
    Reference:
        George E Andrews, Number Theory, Page 15
        An Introduction to the Theory of Numbers, G. H. Hardy, E. M. Wright, Page 294
        Elementary introduction to number theory, Calvin T Long, Page 41

'''

def gcd(a, b):
    while b != 0:
        a, b = b, a % b
    return a

def lcm(x, y):

   lcm = (x*y)//gcd(x,y)
   return lcm

def multiplicative_inverse(e, phi):
    d = 0
    x1 = 0
    x2 = 1
    y1 = 1
    temp_phi = phi
    
    while e > 0:
        temp1 = temp_phi/e
        temp2 = temp_phi - temp1 * e
        temp_phi = e
        e = temp2
        
        x = x2 - temp1 * x1
        y = d - temp1 * y1
        
        x2 = x1
        x1 = x
        d = y1
        y1 = y
    
    # if (temp_phi == 1):
    return d + phi

def generate_keypair(p, q):
    
    while (p == q):

        q = new_random_prime(SIZE);
        
    #n = pq
    n = p * q

    #Phi is the totient of n
    phi = (p-1) * (q-1)

    #Choose an integer e such that e and phi(n) are coprime
    e = random.randrange(1, phi)

    #Use Euclid's Algorithm to verify that e and phi(n) are comprime
    g = gcd(e, phi)
    while g != 1:
        e = random.randrange(1, phi)
        g = gcd(e, phi)

    #Use Extended Euclid's Algorithm to generate the private key
    d = multiplicative_inverse(e, phi)
    
    #Return public and private keypair
    #Public key is (e, n) an(d private key is d, n)
    return ((e, n), (d, n))

if __name__ == '__main__':
    
    x = int (input("Please enter a number for size: "))
    if (x <= 0) :
        print("Invaild number, using default size 5")
        x = SIZE

    p = new_random_prime(x)
    q = new_random_prime(x)

    public, private = generate_keypair(p, q)
    

