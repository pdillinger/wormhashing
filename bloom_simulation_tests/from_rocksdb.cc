/*
Copyright (c) Facebook, Inc. and its affiliates.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

// From RocksDB source code https://github.com/facebook/rocksdb/

#ifdef IMPL_ROCKSDB_DYNAMIC
#define FP_RATE_32BIT 1
#define CACHE_LINE_SIZE 64
static void add(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumProbes = k;
  const uint32_t kTotalBits = m_odd;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    const uint32_t bitpos = h % kTotalBits;
    data_[bitpos / 8] |= (1 << (bitpos % 8));
    h += delta;
  }
  //*** END Copy-paste (with minor clean up) ***//
}

static bool query(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumProbes = k;
  const uint32_t kTotalBits = m_odd;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    const uint32_t bitpos = h % kTotalBits;
    if ((data_[bitpos / 8] & (1 << (bitpos % 8))) == 0) {
      return false;
    }
    h += delta;
  }
  return true;
  //*** END Copy-paste (with minor clean up) ***//
}
#endif

#ifdef IMPL_CACHE_ROCKSDB_DYNAMIC
#define FP_RATE_CACHE 512
#define FP_RATE_32BIT 1
#define CACHE_LINE_SIZE 64
static void add(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumBlocks = cache_len;
  const uint32_t kNumProbes = k;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  uint32_t b = ((h >> 11 | (h << 21)) % kNumBlocks) * (CACHE_LINE_SIZE * 8);
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    // Since CACHE_LINE_SIZE is defined as 2^n, this line will be optimized
    // to a simple and operation by compiler.
    const uint32_t bitpos = b + (h % (CACHE_LINE_SIZE * 8));
    data_[bitpos / 8] |= (1 << (bitpos % 8));
    // Rotate h so that we don't reuse the same bytes.
    h = h / (CACHE_LINE_SIZE * 8) +
        (h % (CACHE_LINE_SIZE * 8)) * (0x20000000U / CACHE_LINE_SIZE);
    h += delta;
  }
  //*** END Copy-paste (with minor clean up) ***//
}

static bool query(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumBlocks = cache_len;
  const uint32_t kNumProbes = k;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  uint32_t b = ((h >> 11 | (h << 21)) % kNumBlocks) * (CACHE_LINE_SIZE * 8);
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    // Since CACHE_LINE_SIZE is defined as 2^n, this line will be optimized
    //  to a simple and operation by compiler.
    const uint32_t bitpos = b + (h % (CACHE_LINE_SIZE * 8));
    uint8_t byteval = data_[bitpos / 8];
    if ((byteval & (1 << (bitpos % 8))) == 0) {
      return false;
    }
    // Rotate h so that we don't reuse the same bytes.
    h = h / (CACHE_LINE_SIZE * 8) +
        (h % (CACHE_LINE_SIZE * 8)) * (0x20000000U / CACHE_LINE_SIZE);
    h += delta;
  }
  return true;
  //*** END Copy-paste (with minor clean up) ***//
}
#endif

#ifdef IMPL_CACHE_ROCKSDB_DYNAMIC_FASTRANGE
#define FP_RATE_CACHE 512
#define FP_RATE_32BIT 1
#define CACHE_LINE_SIZE 64
static void add(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumBlocks = cache_len;
  const uint32_t kNumProbes = k;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  uint64_t wide = (uint64_t)kNumBlocks * (h >> 11 | (h << 21));
  uint32_t b = ((uint32_t)(wide >> 32)) * (CACHE_LINE_SIZE * 8);
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    // Since CACHE_LINE_SIZE is defined as 2^n, this line will be optimized
    // to a simple and operation by compiler.
    const uint32_t bitpos = b + (h % (CACHE_LINE_SIZE * 8));
    data_[bitpos / 8] |= (1 << (bitpos % 8));
    // Rotate h so that we don't reuse the same bytes.
    h = h / (CACHE_LINE_SIZE * 8) +
        (h % (CACHE_LINE_SIZE * 8)) * (0x20000000U / CACHE_LINE_SIZE);
    h += delta;
  }
  //*** END Copy-paste (with minor clean up) ***//
}

static bool query(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumBlocks = cache_len;
  const uint32_t kNumProbes = k;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  uint64_t wide = (uint64_t)kNumBlocks * (h >> 11 | (h << 21));
  uint32_t b = ((uint32_t)(wide >> 32)) * (CACHE_LINE_SIZE * 8);
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    // Since CACHE_LINE_SIZE is defined as 2^n, this line will be optimized
    //  to a simple and operation by compiler.
    const uint32_t bitpos = b + (h % (CACHE_LINE_SIZE * 8));
    uint8_t byteval = data_[bitpos / 8];
    if ((byteval & (1 << (bitpos % 8))) == 0) {
      return false;
    }
    // Rotate h so that we don't reuse the same bytes.
    h = h / (CACHE_LINE_SIZE * 8) +
        (h % (CACHE_LINE_SIZE * 8)) * (0x20000000U / CACHE_LINE_SIZE);
    h += delta;
  }
  return true;
  //*** END Copy-paste (with minor clean up) ***//
}
#endif

#ifdef IMPL_CACHE_ROCKSDB_DYNAMIC_FASTRANGE2
#define FP_RATE_CACHE 512
#define FP_RATE_32BIT 1
#define CACHE_LINE_SIZE 64
static void add(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumBlocks = cache_len;
  const uint32_t kNumProbes = k;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  uint64_t wide = (uint64_t)kNumBlocks * h;
  uint32_t b = ((uint32_t)(wide >> 32)) * (CACHE_LINE_SIZE * 8);
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    // Since CACHE_LINE_SIZE is defined as 2^n, this line will be optimized
    // to a simple and operation by compiler.
    const uint32_t bitpos = b + (h % (CACHE_LINE_SIZE * 8));
    data_[bitpos / 8] |= (1 << (bitpos % 8));
    // Rotate h so that we don't reuse the same bytes.
    h = h / (CACHE_LINE_SIZE * 8) +
        (h % (CACHE_LINE_SIZE * 8)) * (0x20000000U / CACHE_LINE_SIZE);
    h += delta;
  }
  //*** END Copy-paste (with minor clean up) ***//
}

static bool query(uint64_t hh) {
  uint32_t h = (uint32_t)hh;
  const uint32_t kNumBlocks = cache_len;
  const uint32_t kNumProbes = k;
  uint8_t * const data_ = reinterpret_cast<uint8_t *>(table);

  //*** BEGIN Copy-paste (with minor clean up) ***//
  const uint32_t delta = (h >> 17) | (h << 15);  // Rotate right 17 bits
  uint64_t wide = (uint64_t)kNumBlocks * h;
  uint32_t b = ((uint32_t)(wide >> 32)) * (CACHE_LINE_SIZE * 8);
  for (uint32_t i = 0; i < kNumProbes; ++i) {
    // Since CACHE_LINE_SIZE is defined as 2^n, this line will be optimized
    //  to a simple and operation by compiler.
    const uint32_t bitpos = b + (h % (CACHE_LINE_SIZE * 8));
    uint8_t byteval = data_[bitpos / 8];
    if ((byteval & (1 << (bitpos % 8))) == 0) {
      return false;
    }
    // Rotate h so that we don't reuse the same bytes.
    h = h / (CACHE_LINE_SIZE * 8) +
        (h % (CACHE_LINE_SIZE * 8)) * (0x20000000U / CACHE_LINE_SIZE);
    h += delta;
  }
  return true;
  //*** END Copy-paste (with minor clean up) ***//
}
#endif
