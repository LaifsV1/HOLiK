#!/bin/bash
file2=out/results.txt
for file in *.out
do
  name=${file%.*}

  errors=$(head -1 $file)
  errorsnum=$(grep -Eo '[0-9]*' <<< $errors)

  grepreal=$(grep -P "real\t" $file)
  minutesM=$(grep -Eo "[0-9]*m" <<< $grepreal)
  secondsS=$(grep -Eo "[0-9]\.[0-9]*s" <<< $grepreal)
  minutes=${minutesM%m}
  seconds=${secondsS%s}
  time=$(echo "60 * $minutes + $seconds" | bc)
  echo $name,$errorsnum,$time >> out/table.csv
done
