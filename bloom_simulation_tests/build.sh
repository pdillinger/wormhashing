#! /bin/bash

GPP=g++
which g++.par 2>/dev/null >/dev/null && GPP=g++.par
which $GPP || GPP=""

CLANGPP=clang++
which clang++.par 2>/dev/null >/dev/null && CLANGPP=clang++.par
which $CLANGPP || CLANGPP=""

ICC=icc
[ -x ~/intel/bin/icc ] && ICC=~/intel/bin/icc
which $ICC || ICC=""

[ "$IMPLS" ] || IMPLS="`grep '[#]ifdef' foo.cc from_rocksdb.cc | grep -o 'IMPL_[^ ]*'`"

for IMPL in $IMPLS; do
  for FIXED_K in any 8 6 3; do
    if [ "$FIXED_K" = "any" ]; then
      KOPT=""
    else
      KOPT="-DFIXED_K=$FIXED_K"
    fi
    if [ "$GPP" ]; then
      CMD="$GPP -D$IMPL $KOPT -std=c++11 -march=native -mtune=native -O9 -o foo_gcc_${IMPL}_${FIXED_K}.out foo.cc"
      echo "$CMD"
      $CMD &
    else
      echo "NOTE: Skipping g++ build; compiler not found"
    fi
    if [ "$CLANGPP" ]; then
      CMD="$CLANGPP -D$IMPL $KOPT -std=c++11 -march=native -mtune=native -Ofast -o foo_clang_${IMPL}_${FIXED_K}.out foo.cc"
      echo "$CMD"
      $CMD &
    else
      echo "NOTE: Skipping clang build; compiler not found"
    fi
    if [ "$ICC" ]; then
      CMD="$ICC -D$IMPL $KOPT -std=c++11 -march=native -mtune=native -Ofast -o foo_intel_${IMPL}_${FIXED_K}.out foo.cc"
      echo "$CMD"
      $CMD &
    else
      echo "NOTE: Skipping clang build; compiler not found"
    fi
  done
  wait
done
