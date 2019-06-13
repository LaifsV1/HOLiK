#!/bin/bash
for file in *.holib
do
  for i in 2 3 4 5
  do
    for j in 1 2 3 4 5
    do
      file2=files/${file%.*}$i$j.holib
      cp $file $file2
      var="# set-bounds $i $j #"
      sed -i "1s/.*/$var/" $file2
    done
  done
done
