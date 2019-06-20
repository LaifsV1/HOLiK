#!/bin/bash

final=final/final.csv
rm -f $final

for file in awkward_2 awkward_3 awkward_safe call_no_order call_order cross_reentrancy cross_reentrancy_safe dos_safe double_alloc_1 double_alloc_2 double_alloc_simple double_free double_free_simple file_lock file_lock_param file_write flat_combiner imj_inp11 lock_counter_safe mochi optimistic_safe read reentrancy_2 reentrancy reentrancy_param reentrancy_safe remote_sync_1 remote_sync_2 reservation reverse_counter_safe
do
  printf $file, >> $final
  for i in 2 3 4 5
  do
    for j in 1 2 3
    do
      file2=$file$i$j.txt
      cat $file2 | tr '\n' , >> $final
    done
  done
  echo >> $final
done
