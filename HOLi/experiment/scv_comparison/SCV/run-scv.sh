#!/bin/bash
for file in *.rkt
do
  file2=out/${file%.*}.out
  ( time raco scv $file ) > $file2 2>&1
done
