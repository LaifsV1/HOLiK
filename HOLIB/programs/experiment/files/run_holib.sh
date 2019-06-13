#!/bin/bash
for file in *.holib
do
  result=out/${file%.*}.out
  { time timeout 120 krun --search --pattern "<k> fail </k><trace> T </trace>" $file ; } &> $result
done
