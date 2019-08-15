#! /bin/sh

GPP=g++
which g++.par 2>/dev/null >/dev/null && GPP=g++.par

CMD="$GPP -Wall -std=c++11 -O3 -o check_fixed_sizes.out check_fixed_sizes.cc"
echo "$CMD"
$CMD
