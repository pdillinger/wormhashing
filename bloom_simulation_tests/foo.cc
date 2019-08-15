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

static int64_t *table;
static unsigned m;
static unsigned k;
static unsigned max_n;

static unsigned m_odd = 0;
static unsigned len_odd = 0;
static unsigned cache_len_odd = 0;

static unsigned len;
static unsigned len_mask;
static unsigned cache_len;
static unsigned cache_len_mask;
static unsigned m_mask;
static unsigned bits_len = 0;
static unsigned bits_64_minus_len = 0;
static unsigned bits_m = 0;
static unsigned bits_64_minus_m = 0;

static void clear() {
  std::fill(table, table + len, 0);
}

#ifdef IMPL_WORM64
static void add(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t) h * m_odd;
    uint64_t a = (uint64_t)(h2 >> 64);
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
    h = (uint64_t)h2;// + a;
  }
}

static bool query(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t) h * m_odd;
    uint64_t a = (uint64_t)(h2 >> 64);
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h = (uint64_t)h2;// + a;
  }
}
#endif

#ifdef IMPL_WORM64_CLEAN1
static inline void mul64(uint64_t a, uint64_t b,
                         uint64_t &upper, uint64_t &lower) {
  uint128_t r = (uint128_t)a * b;
  lower = (uint64_t)r;
  upper = (uint64_t)(r >> 64);
}

static void add(uint64_t h) {
  for (unsigned i = 0; i < k; ++i) {
    uint64_t bit_index;
    mul64(h, m_odd, /*out*/bit_index, /*out*/h);
    table[bit_index >> 6] |= ((uint64_t)1 << (bit_index & 63));
  }
}

static bool query(uint64_t h) {
  for (unsigned i = 0; i < k; ++i) {
    uint64_t bit_index;
    mul64(h, m_odd, /*out*/bit_index, /*out*/h);
    if ((table[bit_index >> 6] & ((uint64_t)1 << (bit_index & 63))) == 0) {
      return false;
    }
  }
  return true;
}
#endif

#ifdef IMPL_WORM64_CLEAN2
static void add(uint64_t h) {
  for (unsigned i = 0; i < k; ++i) {
    uint128_t wide_product = (uint128_t)h * m_odd;
    uint64_t bit_index = (uint64_t)(wide_product >> 64);
    table[bit_index >> 6] |= ((uint64_t)1 << (bit_index & 63));
    h = (uint64_t)wide_product;
  }
}

static bool query(uint64_t h) {
  for (unsigned i = 0; i < k; ++i) {
    uint128_t wide = (uint128_t)h * m_odd;
    uint64_t bit_index = (uint64_t)(wide >> 64);
    if ((table[bit_index >> 6] & ((uint64_t)1 << (bit_index & 63))) == 0) {
      return false;
    }
    h = (uint64_t)wide;
  }
  return true;
}
#endif

#ifdef IMPL_WORM32
#define FP_RATE_32BIT 1
static void add(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  for (unsigned i = 1;; ++i) {
    uint64_t h2 = (uint64_t)h * m_odd;
    uint32_t a = (uint32_t)(h2 >> 32);
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
    h = (uint32_t)h2;// + a;
  }
}

static bool query(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  for (unsigned i = 1;; ++i) {
    uint64_t h2 = (uint64_t) h * m_odd;
    uint32_t a = (uint32_t)(h2 >> 32);
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h = (uint32_t)h2;// + a;
  }
}
#endif

#ifdef IMPL_WORM64_SPLIT_CHEAP
// maybe: move to 32-bit for 5-bit rotation, to be relatively prime to 64

static void add(uint64_t h) {
  uint64_t a = h;
  uint64_t b = h;
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t)a * len_odd;
    table[h2 >> 64] |= ((uint64_t)1 << (b & 63));
    if (i >= k) break;
    a = (uint64_t)h2;
    b++;
    //b = (b >> 6) | (b << 58);
  }
}

static bool query(uint64_t h) {
  uint64_t a = h;
  uint64_t b = h;
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t)a * len_odd;
    if ((table[h2 >> 64] & ((uint64_t)1 << (b & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    a = (uint64_t)h2;
    b++;
    //b = (b >> 6) | (b << 58);
  }
}
#endif

#ifdef IMPL_WORM64_SPLIT_WORM64
static void add(uint64_t h) {
  uint64_t a = h;
  uint64_t b = (h >> 39) | (h << 25);
  uint64_t prev = 0;
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t)a * len_odd;
    uint128_t h3 = (uint128_t)b * 63;
    uint64_t cur = h3 >> 64;
    cur += cur >= prev;
    table[h2 >> 64] |= ((uint64_t)1 << cur);
    if (i >= k) break;
    a = (uint64_t)h2;
    b = (uint64_t)h3;
    prev = cur;
  }
}

static bool query(uint64_t h) {
  uint64_t a = h;
  uint64_t b = (h >> 39) | (h << 25);
  uint64_t prev = 0;
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t)a * len_odd;
    uint128_t h3 = (uint128_t)b * 63;
    uint64_t cur = h3 >> 64;
    cur += cur >= prev;
    if ((table[h2 >> 64] & ((uint64_t)1 << (h3 >> 64))) == 0) {
      return false;
    }
    if (i >= k) return true;
    a = (uint64_t)h2;
    b = (uint64_t)h3;
    prev = cur;
  }
}
#endif

#ifdef IMPL_WORM64_AND_ROT_POW2
static void add(uint64_t h) {
  for (unsigned i = 1;; ++i) {
    {
      uint128_t h2 = (uint128_t) h * m_odd;
      uint64_t a = (uint64_t)(h2 >> 64);
      table[a >> 6] |= ((uint64_t)1 << (a & 63));
      if (i >= k) break;
      h = (uint64_t)h2;
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
      uint128_t h2 = (uint128_t) h * m_odd;
      uint64_t a = (uint64_t)(h2 >> 64);
      if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
        return false;
      }
      if (i >= k) return true;
      h = (uint64_t)h2;// + a;
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
static void add(uint64_t h) {
  uint128_t h2 = (uint128_t) h * m_odd;
  uint64_t a = (uint64_t)(h2 >> 64);
  table[a >> 6] |= ((uint64_t)1 << (a & 63));
  if (k == 1) return;
  h = (uint64_t)h2;// + a;
  for (unsigned i = 2;; ++i) {
    h2 = (uint128_t) h * 511;
    uint64_t b = (uint64_t)(h2 >> 64);
    a ^= b + 1;
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
    h = (uint64_t)h2;// + a;
  }
}

static bool query(uint64_t h) {
  uint128_t h2 = (uint128_t) h * m_odd;
  uint64_t a = (uint64_t)(h2 >> 64);
  if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
    return false;
  }
  if (k == 1) return true;
  h = (uint64_t)h2;// + a;
  for (unsigned i = 2;; ++i) {
    h2 = (uint128_t) h * 511;
    uint64_t b = (uint64_t)(h2 >> 64);
    a ^= b + 1;
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h = (uint64_t)h2;// + a;
  }
}
#endif

#ifdef IMPL_CACHE_WORM64_32
static void add(uint64_t h) {
  uint128_t h2 = (uint128_t) h * m_odd;
  uint64_t a = (uint64_t)(h2 >> 64);
  table[a >> 6] |= ((uint64_t)1 << (a & 63));
  if (k == 1) return;
  uint32_t g = (uint32_t)h2;
  for (unsigned i = 2;; ++i) {
    uint64_t g2 = (uint64_t)g * 511;
    uint32_t b = (uint32_t)(g2 >> 32);
    a ^= b + 1;
    table[a >> 6] |= ((uint64_t)1 << (a & 63));
    if (i >= k) break;
    g = (uint32_t)g2;
  }
}

static bool query(uint64_t h) {
  uint128_t h2 = (uint128_t) h * m_odd;
  uint64_t a = (uint64_t)(h2 >> 64);
  if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
    return false;
  }
  if (k == 1) return true;
  uint32_t g = (uint32_t)h2;
  for (unsigned i = 2;; ++i) {
    uint64_t g2 = (uint64_t)g * 511;
    uint32_t b = (uint32_t)(g2 >> 32);
    a ^= b + 1;
    if ((table[a >> 6] & ((uint64_t)1 << (a & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    g = (uint32_t)g2;
  }
}
#endif

#ifdef IMPL_CACHE_WORM64_ALT
static void add(uint64_t h) {
  uint128_t h2 = (uint128_t)h * cache_len_odd;
  uint64_t a = h2 >> 64;
  a <<= 3;
  h = (uint64_t)h2;
  //uint64_t prev = 0;
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t)h * 511;
    uint64_t cur = h2 >> 64;
    //cur += cur >= prev;
    table[a + (cur >> 6)] |= ((uint64_t)1 << (cur & 63));
    if (i >= k) break;
    h = (uint64_t)h2;
    //prev = cur;
  }
}

static bool query(uint64_t h) {
  uint128_t h2 = (uint128_t)h * cache_len_odd;
  uint64_t a = h2 >> 64;
  a <<= 3;
  h = (uint64_t)h2;
  //uint64_t prev = 0;
  for (unsigned i = 1;; ++i) {
    uint128_t h2 = (uint128_t)h * 511;
    uint64_t cur = h2 >> 64;
    //cur += cur >= prev;
    if ((table[a + (cur >> 6)] & ((uint64_t)1 << (cur & 63))) == 0) {
      return false;
    }
    if (i >= k) return true;
    h = (uint64_t)h2;
    //prev = cur;
  }
}
#endif

#ifdef IMPL_CACHE_WORM64_CHEAP
static void add(uint64_t h) {
  uint128_t h2 = (uint128_t)h * len_odd;
  uint64_t a = h2 >> 64;
  h = (uint64_t)h2;
  for (unsigned i = 0; i < k; ++i) {
    //std::cerr << "At i=" << i << " setting bit " << (h&63) << " at index " << (a ^ i) << std::endl;
    table[a ^ i] |= ((uint64_t)1 << (h & 63));
    h >>= 6;
  }
}

static bool query(uint64_t h) {
  uint128_t h2 = (uint128_t)h * len_odd;
  uint64_t a = h2 >> 64;
  h = (uint64_t)h2;
  for (unsigned i = 0; i < k; ++i) {
    if ((table[a ^ i] & ((uint64_t)1 << (h & 63))) == 0) {
      return false;
    }
    h >>= 6;
  }
  return true;
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
  h = ((uint32_t)h * (uint64_t)m_odd) >> 32;
  for (unsigned i = 1;; ++i) {
    table[h >> 6] |= ((uint64_t)1 << (h & 63));
    if (i >= k) break;
    h += b;
    if (h >= m_odd) h -= m_odd;
  }
}

static bool query(uint64_t h) {
  uint64_t b = (h >> 32) & (m_mask >> 1);
  h = ((uint32_t)h * (uint64_t)m_odd) >> 32;
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

#ifdef IMPL_DBL_PREIMAGE_FASTRANGE32
#define FP_RATE_2IDX 1
static void add(uint64_t h) {
  uint32_t b = h >> 32;
  uint32_t a = (uint32_t)h;
  for (unsigned i = 1;; ++i) {
    uint32_t c = ((uint64_t)a * m_odd) >> 32;
    table[c >> 6] |= ((uint64_t)1 << (c & 63));
    if (i >= k) break;
    a += b;
  }
}

static bool query(uint64_t h) {
  uint32_t b = h >> 32;
  uint32_t a = (uint32_t)h;
  for (unsigned i = 1;; ++i) {
    uint32_t c = ((uint64_t)a * m_odd) >> 32;
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

int main(int argc, char *argv[]) {
  if (argc < 5) {
    std::cerr << "Not enough arguments" << std::endl;
    return 2;
  }
  m = std::atoi(argv[1]);
  m_mask = m - 1;
  len = (((m - 1) | 511) + 1) / 64;
  len_mask = len - 1;
  cache_len = (((m - 1) | 511) + 1) / 512;
  cache_len_mask = len - 1;
  table = new int64_t[len];

  k = std::atoi(argv[2]);

  max_n = (unsigned)(0.69314718 * m / k);

  int seed = std::atoi(argv[3]);
  std::mt19937_64 r(seed);

  int max_total_queries = std::atoi(argv[4]);
  int total_fps = 0;

  int rem_queries_this_structure = 0;

  m_odd = m - ~(m & 1);
  len_odd = len - ~(len & 1);
  cache_len_odd = cache_len - ~(cache_len & 1);

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

  double p = 1.0 - std::exp(- (double) max_n * k / m);
  double e_fp = std::pow(p, k);
  double s_fp = (double)total_fps / max_total_queries;
  bool bad = s_fp > e_fp * 2.0;
  std::cout << argv[0] << " time: " << std::chrono::duration_cast<std::chrono::microseconds>(time_end - time_begin).count() / 1000000.0
    << " sampled_fp_rate" << (bad ? "(!BAD!)" : "") << ": " << s_fp
    << " expected_fp_rate: " << e_fp
#ifdef FP_RATE_2IDX
    << " 2idx_only_rate: " << ((double)max_n / m / m) // TODO: exp
#endif
#ifdef FP_RATE_32BIT
    << " 32bit_only_rate: " << ((double)max_n * std::pow(2, -32)) // TODO: exp
#endif
    << std::endl;
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
$
*/
