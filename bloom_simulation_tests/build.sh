#! /bin/sh

GPP=g++
which g++.par 2>/dev/null >/dev/null && GPP=g++.par
CLANGPP=clang++
which clang++.par 2>/dev/null >/dev/null && CLANGPP=clang++.par
ICC=icc
[ -x ~/intel/bin/icc ] && ICC=~/intel/bin/icc

for IMPL in `grep '[#]ifdef' foo.cc | grep -o 'IMPL_[^ ]*'`; do
  CMD="$GPP -D$IMPL -std=c++11 -march=native -mtune=native -O9 -o foo_gcc_${IMPL}.out foo.cc"
  echo "$CMD"
  $CMD
  CMD="$CLANGPP -D$IMPL -std=c++11 -march=native -mtune=native -Ofast -o foo_clang_${IMPL}.out foo.cc"
  echo "$CMD"
  $CMD
  CMD="$ICC -D$IMPL -std=c++11 -march=native -mtune=native -Ofast -o foo_intel_${IMPL}.out foo.cc"
  echo "$CMD"
  $CMD
done
