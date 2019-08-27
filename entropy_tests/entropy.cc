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
#include <memory>
#include <algorithm>
#include <set>
#include <iostream>
#include <random>
#include <cstdlib>
#include <cmath>

static uint64_t hash(uint64_t v, uint64_t seed = 0) {
  return XXH64(&v, sizeof(v), seed);
}

static uint32_t mix32(uint32_t v) {
  v *= 123456789;
  v = (v << 11) | (v >> 21);
  v *= 123456789;
  v = (v << 11) | (v >> 21);
  v *= 123456789;
  return v;
}

static uint32_t nearest_prime_helper(uint32_t odd, uint32_t sqrt_upper_bound) {
  redo:
  for (uint32_t i = 3; i < sqrt_upper_bound; i += 2) {
    if (odd % i == 0) {
      odd -= 2;
      goto redo;
    }
  }
  return odd;
}

static uint32_t nearest_prime(uint32_t v) {
  if ((v & 1) == 0) {
    v--;
  }
  uint32_t sqrt_upper_bound = 2;
  while (sqrt_upper_bound * sqrt_upper_bound < v) {
    sqrt_upper_bound++;
  }
  return nearest_prime_helper(v, sqrt_upper_bound);
}

int main(int argc, char *argv[]) {
  if (argc < 2) {
    std::cerr << "Not enough arguments" << std::endl;
    return 2;
  }
  int seed = std::atoi(argv[1]);
  std::mt19937_64 r(seed);

  std::vector<bool> seen;
  std::vector<bool> seen_xtra;
  std::vector<bool> seen_inter;
  std::vector<bool> seen_inter_xtra;
  std::set<uint64_t> seen_sparse;
  std::set<uint64_t> seen_sparse_xtra;
  for (int testno = 0; ; testno++) {
    uint32_t start_val = r();
    uint32_t start_val_incr = r() | 1;

    {
      // Test that (various ranges within each test)
      // Going just over with multiples preserves uniqueness (entropy)
      // Using every other result ("interference") is close to that

      const uint32_t max_iterations = 5000000;
      std::vector<uint32_t> configuration;
      std::vector<uint32_t> interference;
      uint64_t product = 1;
      bool last = false;
      for (; !last;) {
        int inner_bits = ((((uint64_t)r()) >> 5) * 31) >> 59;
        uint32_t next_odd = ((uint32_t)r() & ((2 << inner_bits) - 1)) | (2 << inner_bits) | 1;
        //next_odd = nearest_prime(next_odd);
        if (product * next_odd > ((uint64_t)1 << 32)) {
          next_odd = (((uint64_t)1 << 32) / product + 1) | 1;
          last = true;
        }
        configuration.push_back(next_odd);
        product *= next_odd;

        inner_bits = ((((uint64_t)r()) >> 5) * 31) >> 59;
        next_odd = ((uint32_t)r() & ((2 << inner_bits) - 1)) | (2 << inner_bits) | 1;
        //next_odd = nearest_prime(next_odd);
        interference.push_back(next_odd);
      }
      interference[0] = 1;
      seen.clear(); seen.resize(product);
      seen_xtra.clear(); seen_xtra.resize(product);
      seen_inter.clear(); seen_inter.resize(product);
      seen_inter_xtra.clear(); seen_inter_xtra.resize(product);
      int collisions = 0;
      int collisions_xtra = 0;
      int collisions_inter = 0;
      int collisions_inter_xtra = 0;
      for (uint32_t iterations = 0; iterations < max_iterations; iterations++) {
        uint32_t cur = mix32(start_val);
        uint64_t composite = 0;
        uint32_t cur_xtra = cur;
        uint64_t composite_xtra = 0;
        uint32_t cur_inter = cur;
        uint64_t composite_inter = 0;
        uint32_t cur_inter_xtra = cur;
        uint64_t composite_inter_xtra = 0;
        for (unsigned i = 0; i < configuration.size(); i++) {
          uint32_t p = configuration[i];
          uint64_t p64 = p;

          uint32_t upper = (cur * p64) >> 32;
          composite = composite * p + upper;
          cur = cur * p;

          upper = (cur_xtra * p64) >> 32;
          composite_xtra = composite_xtra * p + upper;
          cur_xtra = cur_xtra * p + upper;

          cur_inter *= interference[i];
          upper = (cur_inter * p64) >> 32;
          composite_inter = composite_inter * p + upper;
          cur_inter = cur_inter * p;

          cur_inter_xtra *= interference[i];
          upper = (cur_inter_xtra * p64) >> 32;
          composite_inter_xtra = composite_inter_xtra * p + upper;
          cur_inter_xtra = cur_inter_xtra * p + upper;
        }

        if (seen.at(composite)) {
          collisions++;
        } else {
          seen[composite] = true;
        }
        if (seen_xtra.at(composite_xtra)) {
          collisions_xtra++;
        } else {
          seen_xtra[composite_xtra] = true;
        }
        if (seen_inter.at(composite_inter)) {
          collisions_inter++;
        } else {
          seen_inter[composite_inter] = true;
        }
        if (seen_inter_xtra.at(composite_inter_xtra)) {
          collisions_inter_xtra++;
        } else {
          seen_inter_xtra[composite_inter_xtra] = true;
        }

        start_val += start_val_incr; // overflow ok
      }

      std::cout << "Various#" << testno << ": ";
      for (unsigned i = 0; i < configuration.size(); i++) {
        std::cout << "(" << interference[i] << "*)"
                  << configuration[i];
        if (i + 1 < configuration.size()) {
          std::cout << "*";
        } else {
          std::cout << " ";
        }
      }
      std::cout << "(" << product / 4294967296.0 << ") -> " << collisions << " coll, "
                << collisions_xtra << " xtra, "
                << collisions_inter << " inter, "
                << collisions_inter_xtra << " inter_xtra"
                << std::endl;

      double position = 0.0;
      std::cout << "          ";
      for (unsigned i = 0; i < configuration.size(); i++) {
        position += log2(interference[i]);
        std::cout << "[" << position;
        position += log2(configuration[i]);
        std::cout << "," << position << "]";
      }
      std::cout << std::endl;
    }

    {
      // And test that (various ranges across tests)
      // Using same range and losing order meets entropy expectation
      // TODO? Pairwise values meet expectation

      const uint32_t max_iterations = 1000000;
      int inner_bits = ((((uint64_t)r()) >> 5) * 16) >> 59;
      uint32_t multiplicand = ((uint32_t)r() & ((2 << inner_bits) - 1)) | (2 << inner_bits) | 1;
      //multiplicand = nearest_prime(multiplicand);
      uint32_t power = 1;
      uint64_t product = multiplicand;
      uint64_t rep = ((uint64_t)1 << 32);
      while (product < ((uint64_t)1 << 32)) {
        power++;
        rep *= power;
        product *= multiplicand;
      }

      seen_sparse.clear();
      seen_sparse_xtra.clear();
      std::vector<uint32_t> vals(power);
      int collisions = 0;
      int collisions_xtra = 0;
      for (uint32_t iterations = 0; iterations < max_iterations; iterations++) {
        uint32_t cur = mix32(start_val);
        for (unsigned i = 0; i < power; i++) {
          vals[i] = ((uint64_t)cur * multiplicand) >> 32;
          cur *= multiplicand;
        }

        std::sort(vals.begin(), vals.end());

        uint64_t composite = 0;
        for (unsigned i = 0; i < power; i++) {
          composite = composite * multiplicand + vals[i];
        }

        if (seen_sparse.count(composite) > 0) {
          collisions++;
        } else {
          seen_sparse.insert(composite);
        }

	// xtra
        cur = mix32(start_val);
        for (unsigned i = 0; i < power; i++) {
          uint32_t upper = ((uint64_t)cur * multiplicand) >> 32;
          vals[i] = upper;
          cur = cur * multiplicand + upper;
        }

        std::sort(vals.begin(), vals.end());

        composite = 0;
        for (unsigned i = 0; i < power; i++) {
          composite = composite * multiplicand + vals[i];
        }

        if (seen_sparse_xtra.count(composite) > 0) {
          collisions_xtra++;
        } else {
          seen_sparse_xtra.insert(composite);
        }

        start_val += start_val_incr; // overflow ok
      }

      std::cout << "Same#" << testno << ": "
                << multiplicand << "**" << power << " "
                << "(" << log2(product) << " bits vs. " << log2(rep) << ")"
                << " -> " << collisions << " coll, "
                << collisions_xtra << " xtra" << std::endl;
    }
  }
  return 0;
}

/*
$ ./build.sh
...
$ ./entropy.out $RANDOM
...
*/
