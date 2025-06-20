#!/bin/bash
for class in passes fails
do echo
   echo "$class:"
   for x in riscv-tests/$class/*
   do printf "%-25s " `basename $x`
      cargo r --example sim -q -r -- $x -n 2>&1|tail -2|head -1
   done
done
