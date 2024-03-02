# solver=cvc4
solver=./alethe-check.sh
options="--tlimit=1500 --simplification=none --full-saturate-quant --no-stats"
traces=""
time=""
ulimit="ulimit -S -t 10"
file="alessio.txt"
path="/home/hbarbosa/cvc5/wt-alethe/"

echo "Options: $options"
echo "Traces: $traces"
echo

while read name; do
    echo "$solver on $path$name";
    $ulimit; $time $solver "$path$name" $options $traces;
    echo "=====================================";
done < $file
