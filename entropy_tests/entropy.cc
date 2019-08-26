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
  std::vector<bool> seen_inter;
  std::set<uint64_t> seen_sparse;
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
      seen_inter.clear(); seen_inter.resize(product);
      int collisions = 0;
      int collisions_inter = 0;
      for (uint32_t iterations = 0; iterations < max_iterations; iterations++) {
        uint32_t cur = mix32(start_val);
        uint64_t composite = 0;
        uint32_t cur_inter = cur;
        uint64_t composite_inter = 0;
        for (unsigned i = 0; i < configuration.size(); i++) {
          uint32_t p = configuration[i];
          uint64_t p64 = p;

          uint32_t upper = (cur * p64) >> 32;
          composite = composite * p + upper;
          cur = cur * p; // variant (also works): + upper;

          cur_inter *= interference[i];
          upper = (cur_inter * p64) >> 32;
          composite_inter = composite_inter * p + upper;
          cur = cur * p; // variant (also works): + upper;
        }

        if (seen.at(composite)) {
          collisions++;
        } else {
          seen[composite] = true;
        }
        if (seen_inter.at(composite_inter)) {
          collisions_inter++;
        } else {
          seen_inter[composite_inter] = true;
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
                << collisions_inter << " inter" << std::endl;

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
      std::vector<uint32_t> vals(power);
      int collisions = 0;
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

        start_val += start_val_incr; // overflow ok
      }

      std::cout << "Same#" << testno << ": "
                << multiplicand << "**" << power << " "
                << "(" << log2(product) << " bits vs. " << log2(rep) << ")"
                << " -> " << collisions << " coll" << std::endl;
    }
  }
  return 0;
}

/*
$ ./build.sh
...
$ ./entropy.out $RANDOM
Various#0: (1*)656568545*(21292889*)7 (1.07008) -> 0 coll, 0 inter
          [0,29.2904][53.6342,56.4416]
Same#0: 4681**3 (36.5778 bits vs. 34.585) -> 4 coll
Various#1: (1*)135*(263*)9683629*(183703991*)5 (1.52189) -> 0 coll, 386915 inter
          [0,7.07682][15.1157,38.3229][65.7757,68.0976]
Same#1: 69297**2 (32.161 bits vs. 33) -> 108 coll
Various#2: (1*)246025*(495009*)71*(2593535*)247 (1.00456) -> 0 coll, 7588 inter
          [0,17.9084][36.8255,42.9753][64.2818,72.2301]
Same#2: 3597**3 (35.4377 bits vs. 34.585) -> 96 coll
Various#3: (1*)14015*(10179*)14487*(631864825*)23 (1.08728) -> 0 coll, 0 inter
          [0,13.7747][27.088,40.9105][70.1455,74.6691]
Same#3: 1135**4 (40.5939 bits vs. 36.585) -> 34 coll
Various#4: (1*)1932639*(8941*)2223 (1.0003) -> 0 coll, 0 inter
          [0,20.8821][34.0084,45.1267]
Same#4: 353**4 (33.8541 bits vs. 36.585) -> 1027 coll
Various#5: (1*)9*(95828929*)477218589 (1) -> 0 coll, 0 inter
          [0,3.16993][29.6839,58.514]
Same#5: 5**14 (32.507 bits vs. 62.2523) -> 997223 coll
Various#6: (1*)3435*(140758193*)1250355 (1) -> 0 coll, 1008 inter
          [0,11.7461][38.8147,59.0686]
Same#6: 143**5 (35.7994 bits vs. 38.9069) -> 869 coll
Various#7: (1*)88241483*(11711*)49 (1.00672) -> 0 coll, 0 inter
          [0,26.395][39.9105,45.5252]
Same#7: 15737**3 (41.8256 bits vs. 34.585) -> 0 coll
Various#8: (1*)2069*(3*)2075867 (1) -> 0 coll, 0 inter
          [0,11.0147][12.5997,33.585]
...
*/
