#!/bin/bash

function do_mkrulechecks()
{
  echo "Do grep for rule checks..."
  cat $1 | grep ruleCount > temp-rc.txt
  echo "Clean..."
  sed -i $'s/[^[:print:]\t]//g' temp-rc.txt
  sed -i 's/\[92m+finalProof::ruleCount, \[//g; s/)/\n/g; s/,//g; s/ (//g; s/(//g; s/]\[0m//g; s/ : /,/g' temp-rc.txt
  sed -i '/^$/d' temp-rc.txt
  echo "Aggregate..."
  awk -F, '{a[$1]+=$2;}END{for(i in a)print i", "a[i];}' temp-rc.txt
  rm temp-rc.txt
}

echo "Make regress with stats..."
make regress $@ CVC4_REGRESSION_ARGS="--check-proofs-new --stats" >& temp.txt
do_mkrulechecks temp.txt
rm temp.txt
