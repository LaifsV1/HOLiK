#!/bin/bash
for file in *.holi
do
  for i in 2 3 4 5
  do
    for j in 1 2 3
    do
      file2=files/${file%.*}$i$j.holi
      cp $file $file2
      var="# set-bounds $i $j #"
      sed -i "1s/.*/$var/" $file2
    done
  done
done
