#!/bin/bash

final=final/final.csv
rm -f $final

for file in *.txt
do
  name=${file%.txt}
  printf "$name ," >> $final
  cat $file | tr '\n' , >> $final
  echo >> $final
done
