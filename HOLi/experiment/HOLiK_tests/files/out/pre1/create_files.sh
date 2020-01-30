#!/bin/bash

final=final/final.csv
rm -f $final

#for i in ??????*; do echo "${i%??????}"; done | sort -u | xargs
for file in awkward_2 awkward_2-mo awkward_3 awkward_3-mo awkward_safe awkward_safe-mo call_no_order call_no_order-mo call_order call_order-mo call_order_param call_order_param-mo cross_reentrancy cross_reentrancy-mo cross_reentrancy_safe cross_reentrancy_safe-mo dos_safe dos_safe-mo double_alloc_1 double_alloc_1-mo double_alloc_2 double_alloc_2-mo double_alloc_simple double_alloc_simple-mo double_free double_free-mo double_free_simple double_free_simple-mo file_lock file_lock-mo file_lock_param file_lock_param-mo file_write file_write-mo flat_combiner flat_combiner-mo imj_inp11 imj_inp11-mo lock_counter_safe lock_counter_safe-mo optimistic_safe optimistic_safe-mo read read-mo reentrancy reentrancy_2 reentrancy_2-mo reentrancy-mo reentrancy_param reentrancy_param-mo reentrancy_safe reentrancy_safe-mo remote_sync_1 remote_sync_1-mo remote_sync_2 remote_sync_2-mo reservation reservation-mo reverse_counter_safe reverse_counter_safe-mo small_various_1 small_various_2 small_various_3 small_various_4 various_mains various_mains_no_equiv various_safe various_safe_no_awk various_unsafe various_unsafe_no_equiv
do
  printf $file , >> $final
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
