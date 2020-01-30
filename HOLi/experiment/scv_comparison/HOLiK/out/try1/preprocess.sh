#!/bin/bash
for file in *.out
do
  result=pre/${file%.*}.txt
  { grep -o 'T ==' $file | wc -l | tr '\n' ',' ; } > $result
  { grep -w 'real' $file | sed 's/\<real\>//g' | tr -d " \t" | sed 's/m/:/' | cut -d \. -f1 | sed s/:/*60+/g | bc ; } >> $result
done
