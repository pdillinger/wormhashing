#! /bin/sh

GPP=g++
which g++.par 2>/dev/null >/dev/null && GPP=g++.par

CMD="$GPP -Wall -std=c++11 -O3 -o entropy.out entropy.cc"
echo "$CMD"
$CMD
