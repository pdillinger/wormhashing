#! /bin/sh

GPP=g++
which g++.par 2>/dev/null >/dev/null && GPP=g++.par
CLANGPP=clang++
which clang++.par 2>/dev/null >/dev/null && CLANGPP=clang++.par
ICC=icc
[ -x ~/intel/bin/icc ] && ICC=~/intel/bin/icc
[ "$IMPLS" ] || IMPLS="`grep '[#]ifdef' foo.cc from_rocksdb.cc | grep -o 'IMPL_[^ ]*'`"

for IMPL in $IMPLS; do
  for FIXED_K in any 8; do
    if [ "$FIXED_K" == "any" ]; then
      KOPT=""
    else
      KOPT="-DFIXED_K=$FIXED_K"
    fi
    CMD="$GPP -D$IMPL $KOPT -std=c++11 -march=native -mtune=native -O9 -o foo_gcc_${IMPL}_${FIXED_K}.out foo.cc"
    echo "$CMD"
    $CMD &
    CMD="$CLANGPP -D$IMPL $KOPT -std=c++11 -march=native -mtune=native -Ofast -o foo_clang_${IMPL}_${FIXED_K}.out foo.cc"
    echo "$CMD"
    $CMD &
    CMD="$ICC -D$IMPL $KOPT -std=c++11 -march=native -mtune=native -Ofast -o foo_intel_${IMPL}_${FIXED_K}.out foo.cc"
    echo "$CMD"
    $CMD &
  done
  wait
done
