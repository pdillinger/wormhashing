#include <stdint.h>
#include <iostream>
#include <cstring>

// This program checks for cycles in 32-bit or 64-bit worm hashing
// configurations appropriate for "standard" Bloom filters: generating up to
// 32 values (usually called k for Bloom filters) over a fixed range size
// (usually called m for Bloom filters). Because of associativity of
// multiplication, the starting hash value doesn't matter (except zero) in
// generating a cycle in the carried hash values; with fixed range m, such a
// cycle would manifest only if m**i === 1 (mod word size) for some i where
// 1 <= i <= k.

// We can see from the 32-bit results that there are cycles in cases where
// (m+1) * k >= 2**w (where w is worm hash word size). This can be a practical
// concern for Bloom filters to use 32-bit worm hashing, though filters of
// size 32 MByte minus 3 bits, and smaller, would be fine (for k < 32). (It
// doesn't take long to exhaustively verify all possible m for 32-bit worm
// hashing. See saved_output_32.)

// Even if there are other patterns that would show up in the 64-bit results,
// we can mechanically verify no cycles for any fixed range size up to
// impractical values. See saved_partial_output_64.)

void check32() {
  for (uint32_t v = 1; v != 0; v++) {
    uint32_t p = v;
    for (int i = 2; i <= 32; i++) {
      p *= v;
      if (p == 1) {
        std::cout << "0x" << std::hex << v << std::dec
                  << " ** " << i
                  << " === 1 (mod 2**32)" << std::endl;
        break;
      }
    }
  }
}

void check64() {
  for (uint64_t v = 1;; v += 2) {
    uint64_t p = v;
    for (int i = 2; i <= 32; i++) {
      p *= v;
      if (p == 1) {
        std::cout << "0x" << std::hex << v << std::dec
                  << " ** " << i
                  << " === 1 (mod 2**64)" << std::endl;
        break;
      }
    }
    if ((v & 0x7ffffffffLL) == 1) {
      std::cout << "(" << (v >> 33) << "GB Bloom filter)"
                << std::endl;
    }
  }
}

int main(int argc, char *argv[]) {
  if (argc > 1 && 0 == strcmp(argv[1], "32")) {
    check32();
    return 0;
  } else if (argc > 1 && 0 == strcmp(argv[1], "64")) {
    check64();
    return 0;
  } else {
    std::cerr << "Usage: " << argv[0] << " {32|64} | tee saved_output" << std::endl;
    return 2;
  }
}
