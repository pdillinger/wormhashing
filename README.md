# wormhashing
Source code and validation tests for "worm hashing"

# What is worm hashing?

"Worm hashing" is short for "wide odd regenerative multiplication," a fast, effective, and flexible solution to the problem of
mapping stock hash function results to values needed by hashed data structures, such as Bloom filters. The approach
generalizes [Lemire's fastrange](https://github.com/lemire/fastrange) to generating *many* ranged hash values from a
single stock hash function result.

The key idea is making dual-use of "wide" multiplication, in which the product is twice as wide as each multiplicand. If we
multiply a word-size stock hash function result by a range size, the "upper" word of the wide product is a hash value
uniformly in that range. If that range size is odd, then the "lower" word of the wide product is a re-mixed hash value (Knuth
multiplicative hash) suitable for generating more hash values.

Actual code (64-bit word size, Bloom filter add using k values over range m_odd, C++ with \__uint128_t):

    uint64_t h = XXH64(p, len, /*seed*/0);
    for (unsigned i = 0; i < k; ++i) {
      __uint128_t wide_product = (__uint128_t)h * m_odd;
      uint64_t bit_index = (uint64_t)(wide_product >> 64);
      table[bit_index >> 6] |= ((uint64_t)1 << (bit_index & 63));
      h = (uint64_t)wide_product;
    }

## Word size
We recommend using 64 bit a stock hash function that returns a 64-bit result, like [xxhash64](https://github.com/Cyan4973/xxHash).
This is fast to compute and a single value is accurate enough for practically all non-cryptographic applications.

And multiplying two 64-bit scalars to a 128-bit scalar is quite fast on newer 64-bit processors, including Intel x86 and ARM.
Worm hashing is almost as fast as double hashing with bit masking, which only works for power-of-two range sizes. It is
similar to or faster than adapting alternative techniques such as double hashing with fastrange, and much faster than anything
using modulus. (See [bloom_simulation_tests](bloom_simulation_tests/))

TODO: cycle hazard with 32 bit worm hashing (in addition to inherent accuracy hazard)

## Odd range size
For this simple approach to be regenerative, the range sizes must be odd. (Each multiplication by an even value would stack
zeros in the lowest bits.) We recommend simply subtracting one whenever the desired range size would be even. This should have
negligible or minor impact in almost all applications. For example, leaving one bit unused at the end of a Bloom filter would
only have noticeable impact for extremely small Bloom filters.

It is also common to want a b-bit hash value excluding the all-zeros value. This is easy with worm hashing by using range
(2^b) - 1, which is odd, and then adding one to the result.

## For Bloom filters
Worm hashing should be considered a new standard construction for Bloom filters, vs. using independent hash functions or
double hashing variants. As yet, we have not detected (using [bloom_simulation_tests](bloom_simulation_tests/)) any
significant, repeatable deviation from what you would get with independent hash functions by using 64-bit worm hashing. (The
loss from double hashing and variants is quite detectable for some configurations.)

Aside from getting wide multiplication results, the code is very simple. In fact, being able to pass around a 64-bit hash as a
complete input descriptor can simplify some code.

But be aware: Bloom filter alternatives such as cuckoo filters are generally superior (in speed and accuracy) when memory per
added element is greater than about 8 bits. And in many applications, cache-friendly Bloom filters are much faster than
standard Bloom filters because of locality, with minor accuracy loss.
