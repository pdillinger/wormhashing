/*
Copyright (c) Peter C. Dillinger
Copyright (c) Facebook, Inc. and its affiliates.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#define XXH_INLINE_ALL
#include "../third-party/xxHash/xxhash.h"
#include <stdint.h>
#define uint128_t __uint128_t
#include <algorithm>
#include <iostream>
#include <random>
#include <cstdlib>
#include <cmath>
#include <chrono>

static uint64_t hash(uint64_t v, uint64_t seed = 0) {
  return XXH64(&v, sizeof(v), seed);
}

static inline void wide_mul(size_t a, uint64_t h, size_t &upper, uint64_t &lower) {
#if SIZE_MAX == UINT64_MAX
  // 64-bit. Expect uint128_t to be available
  uint128_t wide = (uint128_t)a * h;
  upper = (uint64_t)(wide >> 64);
  lower = (uint64_t)wide;
#else
  // 32-bit. Use an adequate implementation based on one side being 32-bit.
  uint64_t semiwide = (a & 0xffffffff) * (h & 0xffffffff);
  uint32_t lower_of_lower = (uint32_t)semiwide;
  uint32_t upper_of_lower = (uint32_t)(semiwide >> 32);
  semiwide = (a & 0xffffffff) * (h >> 32);
  semiwide += upper_of_lower;
  upper = (size_t)(semiwide >> 32);
  lower = (semiwide << 32) | lower_of_lower;
#endif
}

static inline size_t fastrange64(size_t a, uint64_t h) {
  size_t rv;
  uint64_t discard;
  wide_mul(a, h, /*out*/rv, /*out*/discard);
  return rv;
}

static inline uint32_t fastrange32(uint32_t a, uint32_t h) {
  uint64_t product = (uint64_t)a * h;
  return (uint32_t)(product >> 32);
}

static inline size_t worm64(size_t a, uint64_t &h) {
  size_t rv;
  wide_mul(a, h, /*out*/rv, /*out*/h);
  return rv;
}

static inline size_t worm64xtra(size_t a, uint64_t &h) {
  size_t rv;
  wide_mul(a, h, /*out*/rv, /*out*/h);
  h += rv;
  return rv;
}

static inline uint32_t worm32(uint32_t a, uint32_t &h) {
  uint64_t product = (uint64_t)a * h;
  h = (uint32_t)product;
  return (uint32_t)(product >> 32);
}

static inline size_t worm64_bits(size_t nbits, uint64_t &h) {
  size_t rv = h >> (64 - nbits);
  h = (h >> (64 - nbits)) | (h << nbits);
  return rv;
}

static inline unsigned round_up_to_pow2(unsigned x) {
  unsigned rv = 1;
  while (rv < x) {
    rv <<= 1;
  }
  return rv;
}

#ifdef FIXED_K
static const unsigned k = FIXED_K;
static const unsigned k_2 = k / 2;
#else
static unsigned k;
static unsigned k_2;
#endif

static int64_t *table;
static unsigned m;
static unsigned max_n;

static unsigned m_odd = 0;
static unsigned len_odd = 0;
static unsigned len_k_2 = 0;
static unsigned len_k_2_odd = 0;
static unsigned len32_odd = 0;
static unsigned cache_len_odd = 0;

static unsigned len;
static unsigned len_mask;
static unsigned cache_len;
static unsigned cache_len_mask;
static unsigned cache256_len;
static unsigned m_mask;
static unsigned bits_len = 0;
static unsigned bits_64_minus_len = 0;
static unsigned bits_m = 0;
static unsigned bits_64_minus_m = 0;

static void clear() {
  std::fill(table, table + len, 0);
}

#ifdef IMPL_NOOP
// For subtracting out the cost of generating the pseudorandom values
static void add(uint64_t h) {
  table[0] |= h;
}

static bool query(uint64_t h) {
  return (table[0] & h) != 0;
}
#endif

#include "from_rocksdb.cc"

#ifdef IMPL_WORM64
static void add(uint64_t h) {
  for (unsigned i = 0; i < k; ++i) {
    size_t a = worm64(m_odd, /*in/out*/h);
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
  }
}

static bool query(uint64_t h) {
  for (unsigned i = 0; i < k; ++i) {
    size_t a = worm64(m_odd, /*in/out*/h);
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
  }
  return true;
}
#endif

#ifdef IMPL_WORM32
#define FP_RATE_32BIT 1
static void add(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  for (unsigned i = 1;; ++i) {
    uint32_t a = worm32(m_odd, /*in/out*/h);
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
  }
}

static bool query(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  for (unsigned i = 1;; ++i) {
    uint32_t a = worm32(m_odd, /*in/out*/h);
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
  }
}
#endif

#ifdef IMPL_WORM64_AND_ROT_POW2
static void add(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    {
      size_t a = worm64(m_odd, /*in/out*/h);
      table[a >> 6] |= ((uint64_t)1 << (a & 63));
      if (i >= k) break;
    }
    ++i;
    {
      unsigned a = h >> bits_64_minus_len;
      unsigned b = ((h >> bits_64_minus_m) & 63);
      table[a] |= (uint64_t)1 << b;
      if (i >= k) break;
      h = (h << (64 - bits_64_minus_m)) | (h >> bits_64_minus_m);
    }
  }
}

static bool query(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    {
      size_t a = worm64(m_odd, /*in/out*/h);
      if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
        return false;
      }
      if (i >= k) return true;
    }
    ++i;
    {
      unsigned a = h >> bits_64_minus_len;
      unsigned b = ((h >> bits_64_minus_m) & 63);
      if ((table[a] & ((uint64_t)1 << b)) == 0) {
        return false;
      }
      if (i >= k) return true;
      h = (h << (64 - bits_64_minus_m)) | (h >> bits_64_minus_m);
    }
  }
}
#endif

#ifdef IMPL_ROT_POW2
static void add(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    table[(h >> 6) & len_mask] |= ((uint64_t)1 << (h & 63));
    if (i >= k) break;
    h = (h >> 39) | (h << 25);
  }
}

static bool query(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    if ((table[(h >> 6) & len_mask] & ((uint64_t)1 << (h & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h = (h >> 39) | (h << 25);
  }
}
#endif

#ifdef IMPL_ROT_POW2_ALT
static void add(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    unsigned a = h >> bits_64_minus_len;
    unsigned b = ((h >> bits_64_minus_m) & 63);
    table[a] |= (uint64_t)1 << b;
    if (i >= k) break;
    h = (h >> 39) | (h << 25);
  }
}

static bool query(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    unsigned a = h >> bits_64_minus_len;
    unsigned b = ((h >> bits_64_minus_m) & 63);
    if ((table[a] & ((uint64_t)1 << b)) == 0) {
      return false;
    }
    if (i >= k) return true;
    h = (h >> 39) | (h << 25);
  }
}
#endif

/*
static inline uint64_t twang_mix64(uint64_t key) noexcept {
  key = (~key) + (key << 21); // key *= (1 << 21) - 1; key -= 1;
  key = key ^ (key >> 24);
  key = key + (key << 3) + (key << 8); // key *= 1 + (1 << 3) + (1 << 8)
  key = key ^ (key >> 14);
  key = key + (key << 2) + (key << 4); // key *= 1 + (1 << 2) + (1 << 4)
  key = key ^ (key >> 28);
  key = key + (key << 31); // key *= 1 + (1 << 31)
  return key;
}
*/

#ifdef IMPL_CACHE_WORM64
#define FP_RATE_CACHE 512
static void add(uint64_t h) {
  size_t a = worm64(m_odd, /*in/out*/h);
  table[a >> 6] |= ((uint64_t)1 << (a & 63));
  if (k == 1) return;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64(511, /*in/out*/h);
    a ^= b + 1;
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
  }
}

static bool query(uint64_t h) {
  size_t a = worm64(m_odd, /*in/out*/h);
  if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
    return false;
  }
  if (k == 1) return true;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64(511, /*in/out*/h);
    a ^= b + 1;
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
  }
}
#endif

#ifdef IMPL_CACHE_WORM64_XTRA
#define FP_RATE_CACHE 512
static void add(uint64_t h) {
  size_t a = worm64xtra(m_odd, /*in/out*/h);
  table[a >> 6] |= ((uint64_t)1 << (a & 63));
  if (k == 1) return;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64xtra(511, /*in/out*/h);
    a ^= b + 1;
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
  }
}

static bool query(uint64_t h) {
  size_t a = worm64xtra(m_odd, /*in/out*/h);
  if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
    return false;
  }
  if (k == 1) return true;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64xtra(511, /*in/out*/h);
    a ^= b + 1;
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
  }
}
#endif

#ifdef IMPL_CACHE_WORM64_ALT
#define FP_RATE_CACHE 512
static void add(uint64_t h) {
  size_t a = worm64(m_odd, /*in/out*/h);
  a <<= 3;
  __builtin_prefetch(table + a, 1, 3);
  //uint64_t prev = 0;
  for (unsigned i = 1;; ++i) {
    size_t cur = worm64(511, /*in/out*/h);
    //cur += cur >= prev;
    table[a + (cur >> 6)] |= ((uint64_t)1 << (cur & 63));
    if (i >= k) break;
    //prev = cur;
  }
}

static bool query(uint64_t h) {
  size_t a = worm64(m_odd, /*in/out*/h);
  a <<= 3;
  __builtin_prefetch(table + a, 0, 3);
  //uint64_t prev = 0;
  for (unsigned i = 1;; ++i) {
    size_t cur = worm64(511, /*in/out*/h);
    //cur += cur >= prev;
    if ((table[a + (cur >> 6)] & ((uint64_t)1 << (cur & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    //prev = cur;
  }
}
#endif

#ifdef IMPL_CACHE_WORM64_FROM32
#define FP_RATE_CACHE 512
#define FP_RATE_32BIT 1
static void add(uint64_t hh) {
  uint32_t h32 = (uint32_t)hh;
  //uint64_t h = (uint64_t)h32 << 32 | h32;
  uint64_t h = (uint64_t)h32 * 9123456789123456789ULL;

  size_t a = worm64(m_odd, /*in/out*/h);
  table[a >> 6] |= ((uint64_t)1 << (a & 63));
  if (k == 1) return;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64(511, /*in/out*/h);
    a ^= b + 1;
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
  }
}

static bool query(uint64_t hh) {
  uint32_t h32 = (uint32_t)hh;
  //uint64_t h = (uint64_t)h32 << 32 | h32;
  uint64_t h = (uint64_t)h32 * 9123456789123456789ULL;

  size_t a = worm64(m_odd, /*in/out*/h);
  if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
    return false;
  }
  if (k == 1) return true;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64(511, /*in/out*/h);
    a ^= b + 1;
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
  }
}
#endif

#ifdef IMPL_LOCAL_WORM64
static void add(uint64_t h) {
  size_t a = worm64(m_odd, /*in/out*/h);
  table[a >> 6] |= ((uint64_t)1 << (a & 63));
  if (k == 1) return;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64(233, /*in/out*/h);
    a += b + 1;
    if (a > m_odd) { a -= m_odd; }
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
  }
}

static bool query(uint64_t h) {
  size_t a = worm64(m_odd, /*in/out*/h);
  if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
    return false;
  }
  if (k == 1) return true;
  for (unsigned i = 2;; ++i) {
    size_t b = worm64(233, /*in/out*/h);
    a += b + 1;
    if (a > m_odd) { a -= m_odd; }
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
  }
}
#endif

#ifdef IMPL_LOCAL_MUL64
static void add(uint64_t h) {
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 1, 3);
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 7; ++j) {
      table[a] |= ((uint64_t)1 << (h & 63));
      ++i;
      if (i >= k) {
        return;
      }
      a += ((h >> 6) & 7);
      if (a >= len_odd) { a -= len_odd; }
      h = (h >> 9) | (h << 55);
    }
  }
}

static bool query(uint64_t h) {
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 1, 3);
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 7; ++j) {
      if ((table[a] & ((uint64_t)1 << (h & 63))) == 0) {
        return false;
      }
      ++i;
      if (i >= k) {
        return true;
      }
      a += ((h >> 6) & 7);
      if (a >= len_odd) { a -= len_odd; }
      h = (h >> 9) | (h << 55);
    }
  }
}
#endif

#ifdef IMPL_CACHE_DBL
#define FP_RATE_CACHE 512
static void add(uint64_t h) {
  size_t a = fastrange64(cache_len, h);
  a <<= 9;
  unsigned b = h & 511;
  unsigned c = (h >> 8) | 1;
  for (unsigned i = 0; i < k; ++i) {
    size_t bit_addr = a + b;
    table[bit_addr >> 6] |= ((uint64_t)1 << (bit_addr & 63));
    b = (b + c) & 511;
  }
}

static bool query(uint64_t h) {
  size_t a = fastrange64(cache_len, h);
  a <<= 9;
  unsigned b = h & 511;
  unsigned c = (h >> 8) | 1;
  for (unsigned i = 0; i < k; ++i) {
    size_t bit_addr = a + b;
    if ((table[bit_addr >> 6] & ((uint64_t)1 << (bit_addr & 63))) == 0) {
      return false;
    }
    b = (b + c) & 511;
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_DBL_BLOCK
#define FP_RATE_CACHE (round_up_to_pow2(k / 2) * 64)
static void add(uint64_t h) {
  // TODO: protect against k > 17 spilling into another cache line, possibly out of bounds
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 0, 3);
  unsigned b = h;
  if (k <= 1) {
    table[a] |= ((uint64_t)1 << (b & 63));
    return;
  }
  unsigned c = (h >> 5) | 1;
  for (unsigned i = 0;; i++) {
    uint64_t mask = ((uint64_t)1 << (b & 63))
                  | ((uint64_t)1 << ((b + c) & 63));
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << ((b + 2 * c) & 63));
      }
      table[a ^ i] |= mask;
      return;
    }
    table[a ^ i] |= mask;
    b += 2 * c;
  }
}

static bool query(uint64_t h) {
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 0, 3);
  unsigned b = h;
  if (k <= 1) {
    return (table[a] & ((uint64_t)1 << (b & 63))) != 0;
  }
  unsigned c = (h >> 5) | 1;
  for (unsigned i = 0;; i++) {
    uint64_t mask = ((uint64_t)1 << (b & 63))
                  | ((uint64_t)1 << ((b + c) & 63));
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << ((b + 2 * c) & 63));
      }
      return (table[a ^ i] & mask) == mask;
    }
    if ((table[a ^ i] & mask) != mask) {
      return false;
    }
    b += 2 * c;
  }
}
#endif

#ifdef IMPL_CACHE_ENHDBL_BLOCK
#define FP_RATE_CACHE (round_up_to_pow2(k / 2) * 64)
static void add(uint64_t h) {
  // TODO: protect against k > 17 spilling into another cache line, possibly out of bounds
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 0, 3);
  unsigned b = h;
  if (k <= 1) {
    table[a] |= ((uint64_t)1 << (b & 63));
    return;
  }
  unsigned c = (h >> 5) | 1;
  for (unsigned i = 0;; i++) {
    uint64_t mask = ((uint64_t)1 << (b & 63))
                  | ((uint64_t)1 << ((b + c) & 63));
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << ((b + 2 * c + i) & 63));
      }
      table[a ^ i] |= mask;
      return;
    }
    table[a ^ i] |= mask;
    b += 2 * c + i;
  }
}

static bool query(uint64_t h) {
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 0, 3);
  unsigned b = h;
  if (k <= 1) {
    return (table[a] & ((uint64_t)1 << (b & 63))) != 0;
  }
  unsigned c = (h >> 5) | 1;
  for (unsigned i = 0;; i++) {
    uint64_t mask = ((uint64_t)1 << (b & 63))
                  | ((uint64_t)1 << ((b + c) & 63));
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << ((b + 2 * c + i) & 63));
      }
      return (table[a ^ i] & mask) == mask;
    }
    if ((table[a ^ i] & mask) != mask) {
      return false;
    }
    b += 2 * c + i;
  }
}
#endif

#ifdef IMPL_CACHE_MUL64
#define FP_RATE_CACHE 512
static void add(uint64_t h) {
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 1, 3);
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 7; ++j) {
      table[a] |= ((uint64_t)1 << (h & 63));
      ++i;
      if (i >= k) {
        return;
      }
      a ^= ((h >> 6) & 7);
      h = (h >> 9) | (h << 55);
    }
  }
}

static bool query(uint64_t h) {
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 1, 3);
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 7; ++j) {
      if ((table[a] & ((uint64_t)1 << (h & 63))) == 0) {
        return false;
      }
      ++i;
      if (i >= k) {
        return true;
      }
      a ^= ((h >> 6) & 7);
      h = (h >> 9) | (h << 55);
    }
  }
}
#endif

#ifdef IMPL_CACHE_MUL64_BLOCK
#define FP_RATE_CACHE (round_up_to_pow2(k / 2) * 64)
static void add(uint64_t h) {
  // TODO: protect against k > 17 spilling into another cache line, possibly out of bounds
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 1, 3);
  if (k <= 1) {
    table[a] |= ((uint64_t)1 << (h & 63));
    return;
  }
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 5; ++j, ++i) {
      uint64_t mask = ((uint64_t)1 << (h & 63))
                    | ((uint64_t)1 << ((h >> 6) & 63));
      if (i + 1 >= k / 2) {
        if (k & 1) {
          mask |= ((uint64_t)1 << ((h >> 12) & 63));
        }
        table[a ^ i] |= mask;
        return;
      }
      table[a ^ i] |= mask;
      h = (h >> 12) | (h << 52);
    }
  }
}

static bool query(uint64_t h) {
  size_t a = fastrange64(len_odd, h);
  __builtin_prefetch(table + a, 0, 3);
  if (k <= 1) {
    return (table[a] & ((uint64_t)1 << (h & 63))) != 0;
  }
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 5; ++j, ++i) {
      uint64_t mask = ((uint64_t)1 << (h & 63))
                    | ((uint64_t)1 << ((h >> 6) & 63));
      if (i + 1 >= k / 2) {
        if (k & 1) {
          mask |= ((uint64_t)1 << ((h >> 12) & 63));
        }
        return (table[a ^ i] & mask) == mask;
      }
      if ((table[a ^ i] & mask) != mask) {
        return false;
      }
      h = (h >> 12) | (h << 52);
    }
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_MUL64_BLOCK_FROM32
#define FP_RATE_CACHE (round_up_to_pow2(k / 2) * 64)
#define FP_RATE_32BIT 1
static void add(uint64_t hh) {
  uint32_t h32 = (uint32_t)hh;
  size_t a = fastrange32(len_odd, h32);
  __builtin_prefetch(table + a, 1, 3);
  uint64_t h = h32;
  if (k <= 1) {
    table[a] |= ((uint64_t)1 << (h & 63));
    return;
  }
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 5; ++j, ++i) {
      uint64_t mask = ((uint64_t)1 << (h & 63))
                    | ((uint64_t)1 << ((h >> 6) & 63));
      if (i + 1 >= k / 2) {
        if (k & 1) {
          mask |= ((uint64_t)1 << ((h >> 12) & 63));
        }
        table[a ^ i] |= mask;
        return;
      }
      table[a ^ i] |= mask;
      h = (h >> 12) | (h << 52);
    }
  }
}

static bool query(uint64_t hh) {
  uint32_t h32 = (uint32_t)hh;
  size_t a = fastrange32(len_odd, h32);
  __builtin_prefetch(table + a, 0, 3);
  uint64_t h = h32;
  if (k <= 1) {
    return (table[a] & ((uint64_t)1 << (h & 63))) != 0;
  }
  for (unsigned i = 0;;) {
    h *= 0x9e3779b97f4a7c13ULL;
    for (int j = 0; j < 5; ++j, ++i) {
      uint64_t mask = ((uint64_t)1 << (h & 63))
                    | ((uint64_t)1 << ((h >> 6) & 63));
      if (i + 1 >= k / 2) {
        if (k & 1) {
          mask |= ((uint64_t)1 << ((h >> 12) & 63));
        }
        return (table[a ^ i] & mask) == mask;
      }
      if ((table[a ^ i] & mask) != mask) {
        return false;
      }
      h = (h >> 12) | (h << 52);
    }
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_WORM64_BLOCK
#define FP_RATE_CACHE (round_up_to_pow2(k / 2) * 64)
static void add(uint64_t h) {
  size_t a = worm64(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 1, 3);
  if (k <= 1) {
    table[a] |= ((uint64_t)1 << (h & 63));
    return;
  }
  for (unsigned i = 0;; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << (h >> 58));
      }
      table[a ^ i] |= mask;
      return;
    }
    table[a ^ i] |= mask;
  }
}

static bool query(uint64_t h) {
  size_t a = worm64(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 0, 3);
  if (k <= 1) {
    return (table[a] & ((uint64_t)1 << (h & 63))) != 0;
  }
  for (unsigned i = 0;; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << (h >> 58));
      }
      return (table[a ^ i] & mask) == mask;
    }
    if ((table[a ^ i] & mask) != mask) {
      return false;
    }
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_WORM64_BLOCK_XTRA
#define FP_RATE_CACHE (round_up_to_pow2(k / 2) * 64)
static void add(uint64_t h) {
  size_t a = worm64xtra(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 1, 3);
  if (k <= 1) {
    table[a] |= ((uint64_t)1 << (h & 63));
    return;
  }
  for (unsigned i = 0;; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64xtra(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << (h >> 58));
      }
      table[a ^ i] |= mask;
      return;
    }
    table[a ^ i] |= mask;
  }
}

static bool query(uint64_t h) {
  size_t a = worm64xtra(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 0, 3);
  if (k <= 1) {
    return (table[a] & ((uint64_t)1 << (h & 63))) != 0;
  }
  for (unsigned i = 0;; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64xtra(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << (h >> 58));
      }
      return (table[a ^ i] & mask) == mask;
    }
    if ((table[a ^ i] & mask) != mask) {
      return false;
    }
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_WORM64_BLOCK_ALT
#define FP_RATE_CACHE (round_up_to_pow2((k + 1) / 2) * 64)
static void add(uint64_t h) {
  size_t a = worm64(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 1, 3);
  for (unsigned i = 0; i < k / 2; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    table[a ^ i] |= mask;
  }
  if (k & 1) {
    size_t b = worm64_bits(6, /*in/out*/h);
    table[a ^ (k/2)] |= ((uint64_t)1 << b);
  }
}

static bool query(uint64_t h) {
  size_t a = worm64(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 0, 3);
  for (unsigned i = 0; i < k / 2; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    if ((table[a ^ i] & mask) != mask) {
      return false;
    }
  }
  if (k & 1) {
    size_t b = worm64_bits(6, /*in/out*/h);
    return (table[a ^ (k/2)] & ((uint64_t)1 << b)) != 0;
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_WORM64_BLOCKPAIR
#define FP_RATE_CACHE ((k / 2) * 64)
static void add(uint64_t h) {
  size_t a = k_2 * worm64(len_k_2_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 1, 3);
  for (unsigned i = 0; i < k_2; ++i) {
    uint64_t mask = ((uint64_t)1 << (h & 63))
                  | ((uint64_t)1 << ((h >> 6) & 63));
    table[a + i] |= mask;
    h >>= 12;
  }
}

static bool query(uint64_t h) {
  size_t a = k_2 * worm64(len_k_2_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 0, 3);
  for (unsigned i = 0; i < k_2; ++i) {
    uint64_t mask = ((uint64_t)1 << (h & 63))
                  | ((uint64_t)1 << ((h >> 6) & 63));
    if ((table[a + i] & mask) != mask) {
      return false;
    }
    h >>= 12;
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_MUL64_BLOCKPAIR
#define FP_RATE_CACHE ((k / 2) * 64)
static void add(uint64_t h) {
  size_t a = k_2 * fastrange64(len_k_2, h);
  __builtin_prefetch(table + a, 1, 3);
  h *= 0x9e3779b97f4a7c13ULL;
  for (unsigned i = 0; i < k_2; ++i) {
    uint64_t mask = ((uint64_t)1 << (h & 63))
                  | ((uint64_t)1 << ((h >> 6) & 63));
    table[a + i] |= mask;
    h >>= 12;
  }
}

static bool query(uint64_t h) {
  size_t a = k_2 * fastrange64(len_k_2, h);
  __builtin_prefetch(table + a, 0, 3);
  h *= 0x9e3779b97f4a7c13ULL;
  for (unsigned i = 0; i < k_2; ++i) {
    uint64_t mask = ((uint64_t)1 << (h & 63))
                  | ((uint64_t)1 << ((h >> 6) & 63));
    if ((table[a + i] & mask) != mask) {
      return false;
    }
    h >>= 12;
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_WORM64_BLOCK_FROM32
#define FP_RATE_CACHE (round_up_to_pow2(k / 2) * 64)
#define FP_RATE_32BIT 1
static void add(uint64_t hh) {
  uint32_t h32 = (uint32_t)hh;
  size_t a = worm32(len_odd, /*in/out*/h32);
  __builtin_prefetch(table + a, 1, 3);
  uint64_t h = 0x9e3779b97f4a7c13ULL * h32;
  if (k <= 1) {
    table[a] |= ((uint64_t)1 << (h & 63));
    return;
  }
  for (unsigned i = 0;; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << (h >> 58));
      }
      table[a ^ i] |= mask;
      return;
    }
    table[a ^ i] |= mask;
  }
}

static bool query(uint64_t hh) {
  uint32_t h32 = (uint32_t)hh;
  size_t a = worm32(len_odd, /*in/out*/h32);
  __builtin_prefetch(table + a, 1, 3);
  uint64_t h = 0x9e3779b97f4a7c13ULL * h32;
  if (k <= 1) {
    return (table[a] & ((uint64_t)1 << (h & 63))) != 0;
  }
  for (unsigned i = 0;; ++i) {
    size_t b = worm64_bits(6, /*in/out*/h);
    size_t c = worm64(63, /*in/out*/h);
    c += c >= b; // uniquify
    uint64_t mask = ((uint64_t)1 << b)
                  | ((uint64_t)1 << c);
    if (i + 1 >= k / 2) {
      if (k & 1) {
        mask |= ((uint64_t)1 << (h >> 58));
      }
      return (table[a ^ i] & mask) == mask;
    }
    if ((table[a ^ i] & mask) != mask) {
      return false;
    }
  }
  return true;
}
#endif

#ifdef IMPL_CACHE_BLOCK64
#define FP_RATE_CACHE 64
static void add(uint64_t h) {
  size_t a = worm64(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 1, 3);
  uint64_t mask = 0;
  for (unsigned i = 0; i < k; ++i) {
    mask |= ((uint64_t)1 << (h & 63));
    h = (h >> 6) | (h << 58);
  }
  table[a] |= mask;
}

static bool query(uint64_t h) {
  size_t a = worm64(len_odd, /*in/out*/h);
  __builtin_prefetch(table + a, 0, 3);
  uint64_t mask = 0;
  for (unsigned i = 0; i < k; ++i) {
    mask |= ((uint64_t)1 << (h & 63));
    h = (h >> 6) | (h << 58);
  }
  return (table[a] & mask) == mask;
}
#endif

#ifdef IMPL_DBL_POW2
#define FP_RATE_2IDX 1
static void add(uint64_t h) {
  uint64_t b = h >> 32;
  for (unsigned i = 1;; ++i) {
    table[(h >> 6) & len_mask] |= ((uint64_t)1 << (h & 63));
    if (i >= k) break;
    h += b;
  }
}

static bool query(uint64_t h) {
  uint64_t b = h >> 32;
  for (unsigned i = 1;; ++i) {
    if ((table[(h >> 6) & len_mask] & ((uint64_t)1 << (h & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h += b;
  }
}
#endif

#ifdef IMPL_DBL_POW2_SPLIT_CHEAP
#define FP_RATE_2IDX 1
static void add(uint64_t h) {
  uint64_t a = h;
  uint64_t b = (h << 32) | (h >> 32);
  uint64_t c = b;
  for (unsigned i = 1;; ++i) {
    table[a & len_mask] |= ((uint64_t)1 << (c & 63));
    if (i >= k) break;
    a += b;
    c++;
  }
}

static bool query(uint64_t h) {
  uint64_t a = h;
  uint64_t b = (h << 32) | (h >> 32);
  uint64_t c = b;
  for (unsigned i = 1;; ++i) {
    if ((table[a & len_mask] & ((uint64_t)1 << (c & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    a += b;
    c++;
  }
}
#endif

#ifdef IMPL_ENH_POW2
#define FP_RATE_2IDX 1
static void add(uint64_t h) {
  uint64_t b = h >> 32;
  for (unsigned i = 1;; ++i) {
    table[(h >> 6) & len_mask] |= ((uint64_t)1 << (h & 63));
    if (i >= k) break;
    h += b;
    b += i;
  }
}

static bool query(uint64_t h) {
  uint64_t b = h >> 32;
  for (unsigned i = 1;; ++i) {
    if ((table[(h >> 6) & len_mask] & ((uint64_t)1 << (h & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h += b;
    b += i;
  }
}
#endif

#ifdef IMPL_DBL_ONE_MOD
#define FP_RATE_2IDX 1
static void add(uint64_t h) {
  uint64_t b = (h >> 32) & (m_mask >> 1);
  h = ((uint32_t)h) % m_odd;
  for (unsigned i = 1;; ++i) {
    table[h >> 6] |= ((uint64_t)1 << (h & 63));
    if (i >= k) break;
    h += b;
    if (h >= m_odd) h -= m_odd;
  }
}

static bool query(uint64_t h) {
  uint64_t b = (h >> 32) & (m_mask >> 1);
  h = ((uint32_t)h) % m_odd;
  for (unsigned i = 1;; ++i) {
    if ((table[h >> 6] & ((uint64_t)1 << (h & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h += b;
    if (h >= m_odd) h -= m_odd;
  }
}
#endif

#ifdef IMPL_DBL_ONE_FASTRANGE32
#define FP_RATE_2IDX 1
static void add(uint64_t h) {
  uint64_t b = (h >> 32) & (m_mask >> 1);
  uint64_t a = fastrange32(m_odd, (uint32_t)h);
  for (unsigned i = 1;; ++i) {
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
    a += b;
    if (a >= m_odd) a -= m_odd;
  }
}

static bool query(uint64_t h) {
  uint64_t b = (h >> 32) & (m_mask >> 1);
  uint64_t a = fastrange32(m_odd, (uint32_t)h);
  for (unsigned i = 1;; ++i) {
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    a += b;
    if (a >= m_odd) a -= m_odd;
  }
}
#endif

#ifdef IMPL_DBL_PREIMAGE_FASTRANGE32
#define FP_RATE_2IDX 1
static void add(uint64_t h) {
  uint32_t b = h >> 32;
  uint32_t a = (uint32_t)h;
  for (unsigned i = 1;; ++i) {
    uint32_t c = fastrange32(m_odd, a);
    table[c >> 6] |= ((uint64_t)1 << (c & 63));
    if (i >= k) break;
    a += b;
  }
}

static bool query(uint64_t h) {
  uint32_t b = h >> 32;
  uint32_t a = (uint32_t)h;
  for (unsigned i = 1;; ++i) {
    uint32_t c = fastrange32(m_odd, a);
    if ((table[c >> 6] & ((uint64_t)1 << (c & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    a += b;
  }
}
#endif

#ifdef IMPL_XXHASH64_POW2
static void add(uint64_t v) {
  for (unsigned i = 1;; ++i) {
    uint64_t h = hash(v, i);
    table[(h >> 6) & len_mask] |= ((uint64_t)1 << (h & 63));
    if (i >= k) break;
  }
}

static bool query(uint64_t v) {
  for (unsigned i = 1;; ++i) {
    uint64_t h = hash(v, i);
    if ((table[(h >> 6) & len_mask] & ((uint64_t)1 << (h & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
  }
}
#endif

#ifdef IMPL_CACHE_SIMD_FASTRANGE32
#define FP_RATE_CACHE 256
#define FP_RATE_32BIT 1
#include <immintrin.h>

__m256i k_selector;
const __m256i list_0_to_7 = _mm256_setr_epi32(0, 1, 2, 3, 4, 5, 6, 7);
const __m256i multipliers =
    _mm256_setr_epi32(1 << 0, 1 << 5, 1 << 10, 1 << 15, 1 << 20,
                      1628273 << 0, 1628273 << 5, 1628273 << 10);

#define SETUP
static void setup() {
  k_selector = _mm256_setr_epi32(k >= 1, k >= 2, k >= 3, k >= 4,
                                 k >= 5, k >= 6, k >= 7, k >= 8);
}

static inline __m256i simd_mask(uint32_t h, int k) {
  // Make eight copies of h
  __m256i v = _mm256_set1_epi32(h);

  // Start the process of selecting k out of 8 sectors to actually use, with
  // basic re-arrangement of values 0 to 7 using bottom bits of
  // hash. (Bits above bottom three will be ignored.)
  __m256i s = _mm256_add_epi32(list_0_to_7, v);

  // Re-mix each hash with various (odd) multipliers
  v = _mm256_mullo_epi32(v, multipliers);

  // Use those 0 to 7 values to permute the k selector 1s.
  s = _mm256_permutevar8x32_epi32(k_selector, s);

  // Shift away all but top 5 re-mixed hash bits
  v = _mm256_srli_epi32(v, 27);

  // Generate mask by left-shifting selected 1s by those hash quantities
  return _mm256_sllv_epi32(s, v);
}

static void add(uint64_t v) {
  uint32_t h = (uint32_t)v;
  uint32_t a = fastrange32(cache256_len, h);
  // Try to start the memory load
  __m256i *ptr = &reinterpret_cast<__m256i*>(table)[a];
  __m256i val = *ptr;
  // Remix with golden ratio after fastrange
  h *= 0x9e3779b9;
  // Like *ptr |= mask;
  _mm256_store_si256(ptr, _mm256_or_si256(val, simd_mask(h, k)));
}

static bool query(uint64_t v) {
  uint32_t h = (uint32_t)v;
  uint32_t a = fastrange32(cache256_len, h);
  __m256i val = reinterpret_cast<__m256i*>(table)[a];
  // Remix with golden ratio after fastrange
  h *= 0x9e3779b9;
  // Like ((~val) & mask) == 0)
  return _mm256_testc_si256(val, simd_mask(h, k));
}
#endif

#ifdef IMPL_CACHE_SIMD_FASTRANGE32_K8
#define FP_RATE_CACHE 256
#define FP_RATE_32BIT 1
// Always k=8
#include <immintrin.h>

static inline __m256i simd_mask(uint32_t h) {
  // Make eight copies of h
  __m256i v = _mm256_set1_epi32(h);
  // Re-mix each with various (odd) multipliers
  v = _mm256_mullo_epi32(v, _mm256_setr_epi32(-1545148375, 939189041,
                                              1323509755, -1969823245,
                                              574551977, -1487628273,
                                              -1264161019, -1720001801));
  // Shift away all but top 5 bits
  v = _mm256_srli_epi32(v, 27);
  // Generate mask by left-shifting 1s by those quantities
  return _mm256_sllv_epi32(_mm256_set1_epi32(1), v);
}

static void add(uint64_t v) {
  uint32_t h = (uint32_t)v;
  uint32_t a = fastrange32(cache256_len, h);
  __m256i *ptr = &reinterpret_cast<__m256i*>(table)[a];
  __m256i val = *ptr;
  h = (h << 21) | (h >> 11);
  // equivalent to *ptr |= mask;
  _mm256_store_si256(ptr, _mm256_or_si256(val, simd_mask(h)));
}

static bool query(uint64_t v) {
  uint32_t h = (uint32_t)v;
  uint32_t a = fastrange32(cache256_len, h);
  __m256i val = reinterpret_cast<__m256i*>(table)[a];
  h = (h << 21) | (h >> 11);
  // equivalent to ((~val) & mask) == 0)
  return _mm256_testc_si256(val, simd_mask(h));
}
#endif

static double bffp(double m, double n, unsigned k) {
  double p = 1.0 - std::exp(- n * k / m);
  return std::pow(p, k);
}

int main(int argc, char *argv[]) {
  if (argc < 6) {
    std::cerr << "Not enough arguments" << std::endl;
    return 2;
  }
  m = std::atoi(argv[1]);
  m_mask = m - 1;
  len = (((m - 1) | 511) + 1) / 64;
  len_mask = len - 1;
  cache_len = (((m - 1) | 511) + 1) / 512;
  cache_len_mask = cache_len - 1;
  cache256_len = (((m - 1) | 255) + 1) / 256;
  table = new int64_t[len + 3];
  while ((uintptr_t)table & 31) { ++table; } // align on 256 bit boundary

#ifdef FIXED_K
  if (k != std::atoi(argv[2])) {
    std::cerr << "Compiled for fixed k=" << k << " so must specify that" << std::endl;
    return 2;
  }
#else
  k = std::atoi(argv[2]);
  k_2 = k / 2;
#endif

  double b = std::atof(argv[3]);
  if (b == 0.0) {
    if (k == 0) {
      std::cerr << "Must specify non-zero for either k or memory factor" << std::endl;
      return 2;
    }
    max_n = (unsigned)(0.69314718 * m / k + 0.5);
  } else {
    max_n = (unsigned)(m / b + 0.5);
#ifndef FIXED_K
    if (k == 0) {
      k = (unsigned)(0.69314718 * b + 0.5);
      k_2 = k / 2;
    }
#endif
  }

  int seed = std::atoi(argv[4]);
  std::mt19937_64 r(seed);

  int max_total_queries = std::atoi(argv[5]);
  int total_fps = 0;

  int rem_queries_this_structure = 0;

  m_odd = m - ~(m & 1);
  len_odd = len - ~(len & 1);
  len32_odd = len * 2 - 1;
  cache_len_odd = cache_len - ~(cache_len & 1);
  len_k_2 = len / k_2;
  len_k_2_odd = len_k_2 - ~(len_k_2 & 1);

  if ((m_mask & m) == 0) {
    // power of 2
    // populate remaining values
    for (int i = 0; i < 64; i++) {
      if (len == ((uint64_t)1 << i)) {
        bits_len = i;
      }
      if (m == ((uint64_t)1 << i)) {
        bits_m = i;
      }
    }
    bits_64_minus_len = 64 - bits_len;
    bits_64_minus_m = 64 - bits_m;
  }
  // check m_odd
  uint64_t prod = m_odd;
  for (unsigned i = 1; i < k; i++) {
    prod *= m_odd;
    if (prod <= 1) {
      std::cout << "Cycle after " << i << std::endl;
      break;
    }
  }
#ifdef SETUP
  setup();
#endif
  std::chrono::steady_clock::time_point time_begin = std::chrono::steady_clock::now();

  // actual run
  for (int total_queries = 0; total_queries < max_total_queries; ++total_queries) {
    if (rem_queries_this_structure == 0) {
      clear();
      rem_queries_this_structure = 10 * max_n;
      for (unsigned i = 0; i < max_n; ++i) {
        add(hash(r()));
      }
    }
    if (query(hash(r()))) {
      total_fps++;
    }
  }

  std::chrono::steady_clock::time_point time_end = std::chrono::steady_clock::now();

  double e_fp = bffp(m, max_n, k);
  double s_fp = (double)total_fps / max_total_queries;
  bool bad = s_fp > e_fp * 2.0;
  std::cout << argv[0] << " time: " << std::chrono::duration_cast<std::chrono::microseconds>(time_end - time_begin).count() / 1000000.0
    << " sampled_fp_rate" << (bad ? "(!BAD!)" : "") << ": " << s_fp
    << " expected_fp_rate: " << e_fp;
#ifdef FP_RATE_CACHE
  double cache_n = (double)max_n / (m / FP_RATE_CACHE);
  std::cout << " cache_line_rate(" << FP_RATE_CACHE << "): "
    << (bffp(FP_RATE_CACHE, cache_n + std::sqrt(cache_n), k)
      + bffp(FP_RATE_CACHE, cache_n - std::sqrt(cache_n), k)) / 2.0;
#endif
#ifdef FP_RATE_2IDX
  std::cout << " 2idx_only_addl: " << ((double)max_n / m / m); // TODO: exp
#endif
#ifdef FP_RATE_32BIT
  std::cout << " 32bit_only_addl: " << ((double)max_n * std::pow(2, -32)); // TODO: exp
#endif
  std::cout << std::endl;
  return 0;
}

/*
$ ./build.sh
...
$ #########################################
$ # General speed and accuracy validation #
$ #########################################
$ (M=8192; K=8; S=$RANDOM; Q=2100000000; for COMP in gcc clang intel; do for IMPL in foo_${COMP}_IMPL*; do ./$IMPL $M $K $S $Q & done; wait; done) | tee foo_out_all~
./foo_gcc_IMPL_DBL_POW2_SPLIT_CHEAP.out time: 51.5557 sampled_fp_rate(!BAD!): 0.0476665 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_gcc_IMPL_ROT_POW2_ALT.out time: 51.6645 sampled_fp_rate: 0.00398897 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_DBL_POW2.out time: 51.7164 sampled_fp_rate: 0.00377187 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_gcc_IMPL_ROT_POW2.out time: 51.7716 sampled_fp_rate: 0.00423194 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_ENH_POW2.out time: 52.5657 sampled_fp_rate: 0.00388034 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_gcc_IMPL_CACHE_WORM64_CHEAP.out time: 53.1637 sampled_fp_rate: 0.0053336 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_WORM64_SPLIT_CHEAP.out time: 53.3573 sampled_fp_rate: 0.00409301 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_DBL_ONE_FASTRANGE32.out time: 54.6633 sampled_fp_rate: 0.00389972 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_gcc_IMPL_WORM64.out time: 54.6814 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_WORM32.out time: 54.9324 sampled_fp_rate: 0.00389894 expected_fp_rate: 0.00388242 32bit_only_rate: 1.65077e-07
./foo_gcc_IMPL_WORM64_CLEAN2.out time: 54.9735 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_DBL_PREIMAGE_FASTRANGE32.out time: 55.14 sampled_fp_rate: 0.00357752 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_gcc_IMPL_WORM64_CLEAN1.out time: 55.2517 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_CACHE_WORM64.out time: 55.3133 sampled_fp_rate: 0.00488674 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_CACHE_WORM64_32.out time: 55.5303 sampled_fp_rate: 0.00466851 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_CACHE_WORM64_ALT.out time: 55.6549 sampled_fp_rate: 0.00427114 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_WORM64_SPLIT_WORM64.out time: 56.0708 sampled_fp_rate: 0.00372237 expected_fp_rate: 0.00388242
./foo_gcc_IMPL_DBL_ONE_MOD.out time: 66.6105 sampled_fp_rate: 0.00393361 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_gcc_IMPL_XXHASH64_POW2.out time: 87.8655 sampled_fp_rate: 0.00362455 expected_fp_rate: 0.00388242
./foo_clang_IMPL_ENH_POW2.out time: 52.2552 sampled_fp_rate: 0.00388034 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_clang_IMPL_ROT_POW2_ALT.out time: 52.3042 sampled_fp_rate: 0.00398897 expected_fp_rate: 0.00388242
./foo_clang_IMPL_DBL_POW2.out time: 52.5767 sampled_fp_rate: 0.00377187 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_clang_IMPL_DBL_POW2_SPLIT_CHEAP.out time: 53.7373 sampled_fp_rate(!BAD!): 0.0476665 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_clang_IMPL_ROT_POW2.out time: 54.3327 sampled_fp_rate: 0.00423194 expected_fp_rate: 0.00388242
./foo_clang_IMPL_CACHE_WORM64_CHEAP.out time: 54.9897 sampled_fp_rate: 0.0053336 expected_fp_rate: 0.00388242
./foo_clang_IMPL_WORM64_SPLIT_CHEAP.out time: 55.1691 sampled_fp_rate: 0.00409301 expected_fp_rate: 0.00388242
./foo_clang_IMPL_DBL_PREIMAGE_FASTRANGE32.out time: 55.2342 sampled_fp_rate: 0.00357752 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_clang_IMPL_DBL_ONE_FASTRANGE32.out time: 55.958 sampled_fp_rate: 0.00389972 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_clang_IMPL_WORM64_SPLIT_WORM64.out time: 55.975 sampled_fp_rate: 0.00372237 expected_fp_rate: 0.00388242
./foo_clang_IMPL_WORM64_CLEAN2.out time: 56.2808 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_clang_IMPL_WORM64_CLEAN1.out time: 56.9465 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_clang_IMPL_WORM32.out time: 57.3561 sampled_fp_rate: 0.00389894 expected_fp_rate: 0.00388242 32bit_only_rate: 1.65077e-07
./foo_clang_IMPL_CACHE_WORM64.out time: 57.6597 sampled_fp_rate: 0.00488674 expected_fp_rate: 0.00388242
./foo_clang_IMPL_CACHE_WORM64_32.out time: 57.9262 sampled_fp_rate: 0.00466851 expected_fp_rate: 0.00388242
./foo_clang_IMPL_WORM64.out time: 58.5065 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_clang_IMPL_CACHE_WORM64_ALT.out time: 59.6637 sampled_fp_rate: 0.00427114 expected_fp_rate: 0.00388242
./foo_clang_IMPL_DBL_ONE_MOD.out time: 68.9527 sampled_fp_rate: 0.00393361 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_clang_IMPL_XXHASH64_POW2.out time: 77.5053 sampled_fp_rate: 0.00362455 expected_fp_rate: 0.00388242
./foo_intel_IMPL_DBL_POW2.out time: 54.5709 sampled_fp_rate: 0.00377187 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_intel_IMPL_DBL_POW2_SPLIT_CHEAP.out time: 54.6726 sampled_fp_rate(!BAD!): 0.0476665 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_intel_IMPL_ROT_POW2_ALT.out time: 55.0455 sampled_fp_rate: 0.00398897 expected_fp_rate: 0.00388242
./foo_intel_IMPL_CACHE_WORM64_CHEAP.out time: 55.2811 sampled_fp_rate: 0.0053336 expected_fp_rate: 0.00388242
./foo_intel_IMPL_ROT_POW2.out time: 55.3422 sampled_fp_rate: 0.00423194 expected_fp_rate: 0.00388242
./foo_intel_IMPL_ENH_POW2.out time: 55.9975 sampled_fp_rate: 0.00388034 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_intel_IMPL_WORM64_SPLIT_WORM64.out time: 57.133 sampled_fp_rate: 0.00372237 expected_fp_rate: 0.00388242
./foo_intel_IMPL_WORM64_CLEAN1.out time: 57.1405 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_intel_IMPL_WORM64_SPLIT_CHEAP.out time: 57.186 sampled_fp_rate: 0.00409301 expected_fp_rate: 0.00388242
./foo_intel_IMPL_WORM64_CLEAN2.out time: 57.4063 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_intel_IMPL_DBL_ONE_FASTRANGE32.out time: 57.4535 sampled_fp_rate: 0.00389972 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_intel_IMPL_CACHE_WORM64_ALT.out time: 57.5109 sampled_fp_rate: 0.00427111 expected_fp_rate: 0.00388242
./foo_intel_IMPL_CACHE_WORM64_32.out time: 57.8917 sampled_fp_rate: 0.00466851 expected_fp_rate: 0.00388242
./foo_intel_IMPL_WORM64.out time: 57.8876 sampled_fp_rate: 0.00417671 expected_fp_rate: 0.00388242
./foo_intel_IMPL_CACHE_WORM64.out time: 58.5642 sampled_fp_rate: 0.00488674 expected_fp_rate: 0.00388242
./foo_intel_IMPL_WORM32.out time: 58.8961 sampled_fp_rate: 0.00389894 expected_fp_rate: 0.00388242 32bit_only_rate: 1.65077e-07
./foo_intel_IMPL_DBL_PREIMAGE_FASTRANGE32.out time: 59.3894 sampled_fp_rate: 0.00357752 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_intel_IMPL_DBL_ONE_MOD.out time: 70.6138 sampled_fp_rate: 0.00393361 expected_fp_rate: 0.00388242 2idx_only_rate: 1.05649e-05
./foo_intel_IMPL_XXHASH64_POW2.out time: 93.1562 sampled_fp_rate: 0.00362455 expected_fp_rate: 0.00388242
$ ##################################################
$ # Double hashing (unenhanced) considered harmful #
$ ##################################################
$ (M=1024; K=20; S=$RANDOM; Q=100000000; for IMPL in foo_gcc_IMPL_{DBL_POW2,ENH_POW2,DBL_PREIMAGE_FASTRANGE32}.out; do ./$IMPL $M $K $S $Q & done; wait)
./foo_gcc_IMPL_DBL_POW2.out time: 2.53919 sampled_fp_rate(!BAD!): 0.00128546 expected_fp_rate: 7.86357e-07 2idx_only_rate: 3.33786e-05
./foo_gcc_IMPL_ENH_POW2.out time: 2.61996 sampled_fp_rate(!BAD!): 3.452e-05 expected_fp_rate: 7.86357e-07 2idx_only_rate: 3.33786e-05
./foo_gcc_IMPL_DBL_PREIMAGE_FASTRANGE32.out time: 2.72675 sampled_fp_rate(!BAD!): 0.00016276 expected_fp_rate: 7.86357e-07 2idx_only_rate: 3.33786e-05
$ #########################################
$ # 32-bit worm not generally recommended #
$ #########################################
$ (M=$((16 * 8 * 1024 * 1024)); K=12; S=$RANDOM; Q=100000000; for IMPL in foo_gcc_IMPL_WORM{32,64}.out; do ./$IMPL $M $K $S $Q & done; wait)
./foo_gcc_IMPL_WORM32.out time: 8.61897 sampled_fp_rate(!BAD!): 0.0454721 expected_fp_rate: 0.00024414 32bit_only_rate: 0.00180507
./foo_gcc_IMPL_WORM64.out time: 9.02976 sampled_fp_rate: 0.0002447 expected_fp_rate: 0.00024414
$ #####################################################
$ # Intermingling ROT with WORM seems OK for accuracy #
$ #####################################################
$ (M=65536; K=20; S=$RANDOM; Q=500000000; for IMPL in foo_intel_IMPL_{ENH_POW2,WORM64,WORM64_AND_ROT_POW2,ROT_POW2_ALT}.out; do ./$IMPL $M $K $S $Q & done; wait)
./foo_intel_IMPL_ROT_POW2_ALT.out time: 12.7548 sampled_fp_rate(!BAD!): 2.654e-06 expected_fp_rate: 9.51902e-07
./foo_intel_IMPL_ENH_POW2.out time: 13.2007 sampled_fp_rate: 1.614e-06 expected_fp_rate: 9.51902e-07 2idx_only_rate: 5.28758e-07
./foo_intel_IMPL_WORM64.out time: 13.7879 sampled_fp_rate: 8.5e-07 expected_fp_rate: 9.51902e-07
./foo_intel_IMPL_WORM64_AND_ROT_POW2.out time: 13.9317 sampled_fp_rate: 8.96e-07 expected_fp_rate: 9.51902e-07
$ ####################################################
$ # Testing optimized cache-friendly implementations #
$ ####################################################
$ (M=$((12345678)); K=8; S=$RANDOM; Q=500000000; for IMPL in foo_gcc_IMPL_{NOOP,WORM64,CACHE_*}.out; do ./$IMPL $M $K $S $Q & done; wait)
./foo_gcc_IMPL_NOOP.out time: 4.43283 sampled_fp_rate(!BAD!): 1 expected_fp_rate: 0.00390624
./foo_gcc_IMPL_CACHE_BLOCK64.out time: 9.9762 sampled_fp_rate(!BAD!): 0.0146745 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_CACHE_MUL64_BLOCK_ALT.out time: 11.8424 sampled_fp_rate: 0.00520687 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_CACHE_MUL64_BLOCK.out time: 12.2904 sampled_fp_rate: 0.00520687 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_CACHE_MUL64_BLOCK2.out time: 12.4896 sampled_fp_rate: 0.00635501 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_CACHE_MUL64_CHEAP.out time: 16.446 sampled_fp_rate: 0.00649212 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_CACHE_MUL32_CHEAP.out time: 16.5504 sampled_fp_rate: 0.00688178 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_gcc_IMPL_CACHE_MUL64_CHEAP2.out time: 16.9667 sampled_fp_rate: 0.00651935 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_CACHE_MUL64_CHEAP_FROM32.out time: 17.3975 sampled_fp_rate: 0.00675398 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_gcc_IMPL_CACHE_ROCKSDB_DYNAMIC_FASTRANGE2.out time: 17.5808 sampled_fp_rate: 0.00658098 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_gcc_IMPL_CACHE_WORM64.out time: 17.6535 sampled_fp_rate: 0.00500722 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_CACHE_ROCKSDB_DYNAMIC_FASTRANGE.out time: 18.3648 sampled_fp_rate: 0.00540961 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_gcc_IMPL_CACHE_WORM64_FROM32.out time: 18.3706 sampled_fp_rate: 0.00527092 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_gcc_IMPL_CACHE_WORM64_ALT.out time: 19.1099 sampled_fp_rate: 0.00509363 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_gcc_IMPL_WORM64.out time: 19.5882 sampled_fp_rate: 0.00390409 expected_fp_rate: 0.00390624
./foo_gcc_IMPL_CACHE_ROCKSDB_DYNAMIC.out time: 21.8537 sampled_fp_rate: 0.00529048 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
$ ################################################
$ # Testing compiled with fixed k vs. variable k #
$ ################################################
$ (M=$((12345678)); K=8; S=$RANDOM; Q=500000000; for IMPL in foo_clang_IMPL_{NOOP,CACHE_MUL*,CACHE_BLOCK*}_{8,any}.out; do ./$IMPL $M $K $S $Q & done; wait)
./foo_clang_IMPL_NOOP_8.out time: 5.081 sampled_fp_rate(!BAD!): 1 expected_fp_rate: 0.00390624
./foo_clang_IMPL_NOOP_any.out time: 5.10355 sampled_fp_rate(!BAD!): 1 expected_fp_rate: 0.00390624
./foo_clang_IMPL_CACHE_BLOCK64_8.out time: 9.28827 sampled_fp_rate(!BAD!): 0.0146606 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_BLOCK64_any.out time: 10.6522 sampled_fp_rate(!BAD!): 0.0146606 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_BLOCK_ALT_8.out time: 11.2642 sampled_fp_rate: 0.00522023 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_BLOCK_8.out time: 11.5023 sampled_fp_rate: 0.00522023 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_BLOCK2_8.out time: 11.6621 sampled_fp_rate: 0.00635194 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_BLOCK_ALT_any.out time: 12.4865 sampled_fp_rate: 0.00522023 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_BLOCK_any.out time: 12.7215 sampled_fp_rate: 0.00522023 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_BLOCK2_any.out time: 13.4629 sampled_fp_rate: 0.00635194 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL32_CHEAP_8.out time: 15.863 sampled_fp_rate: 0.00682816 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_clang_IMPL_CACHE_MUL64_CHEAP_8.out time: 16.258 sampled_fp_rate: 0.00652367 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_CHEAP2_8.out time: 16.4654 sampled_fp_rate: 0.00651982 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_CHEAP_any.out time: 16.6106 sampled_fp_rate: 0.00652367 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
./foo_clang_IMPL_CACHE_MUL64_CHEAP_FROM32_8.out time: 16.7128 sampled_fp_rate: 0.00676554 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_clang_IMPL_CACHE_MUL32_CHEAP_any.out time: 16.8505 sampled_fp_rate: 0.00682816 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_clang_IMPL_CACHE_MUL64_CHEAP_FROM32_any.out time: 17.047 sampled_fp_rate: 0.00676554 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214 32bit_only_addl: 0.000249052
./foo_clang_IMPL_CACHE_MUL64_CHEAP2_any.out time: 17.2786 sampled_fp_rate: 0.00651982 expected_fp_rate: 0.00390624 cache_line_rate: 0.00492214
$
*/
