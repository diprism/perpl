#!/bin/bash

### Modify these if you want to to decrease the time benchmarks take to run

# Number of times hyperfine runs each sample before averaging
hyperfine_runs=10 # default: 10

# Check up to this string length
perpl_range=80 # default: 80
dice_range=20 # default: 20

# For each method, run {5, 10, ..., 45, 50} samples followed by this many zeros
wppl_rejection_samples=000000 # default: 000000
wppl_smc_samples=00000 # default: 00000
wppl_incrementalmh_samples=000000 # default: 000000
wppl_mcmc_samples=000000 # default: 000000

###

curdir=$(pwd)
cd $(dirname "$0")
pwd
wppl_cmd=webppl
perplc_cmd="../../perplc"
dice_cmd="dice"
sumprod="../../fggs/bin/sum_product.py"
fggs=$(dirname $(dirname $(readlink -f "$sumprod")))
export PYTHONPATH="$fggs:$PYTHONPATH"

hyperfine --export-json pcfg-perpl.json \
          --export-csv  pcfg-perpl.csv  \
          --runs "$hyperfine_runs" \
          --parameter-scan length 1 "$perpl_range" \
          --setup "./pcfg-gen-perpl {length} >/tmp/{length}.perpl" \
          --cleanup "rm /tmp/{length}.perpl" \
          "$perplc_cmd /tmp/{length}.perpl | $sumprod -d -m fixed-point -l 1e-50 /dev/stdin"

hyperfine --export-json pcfg-dice.json \
          --export-csv  pcfg-dice.csv  \
          --runs "$hyperfine_runs" \
          --show-output \
          --parameter-scan length 1 "$dice_range" \
          --setup "./pcfg-gen-dice {length} >/tmp/{length}.dice" \
          --cleanup "rm /tmp/{length}.dice" \
          "$dice_cmd -skip-table /dev/stdin </tmp/{length}.dice"


hyperfine --export-json pcfg-wppl.json \
          --export-csv  pcfg-wppl.csv  \
          --runs "$hyperfine_runs" \
          --parameter-list size '5,10,15,20,25,30,35,40,45,50' \
          --parameter-list method "$wppl_rejection_samples rejection,$wppl_smc_samples SMC,$wppl_incrementalmh_samples incrementalMH,$wppl_mcmc_samples MCMC" \
          --setup "./pcfg-gen-wppl {size}{method} | $wppl_cmd /dev/stdin --compile --out '/tmp/{size}{method}.js'" \
          --style none --output inherit \
          --cleanup "rm '/tmp/{size}{method}.js'" \
          --ignore-failure \
          "node '/tmp/{size}{method}.js'" &>"pcfg-wppl.out"

perl accuracy-scatterplot

./pcfg-exact.hs > pcfg-exact.tsv

# The --parameter-list below is computed using pcfg-pac.mpl
hyperfine --export-json pcfg-pac.json \
          --export-csv  pcfg-pac.csv  \
          --runs "$hyperfine_runs" \
          --parameter-list size 159,17484,103730,468570,1851340,6886680,24346848,83030798,274706448,906160275  \
          --setup "./pcfg-gen-wppl {size} rejection | $wppl_cmd /dev/stdin --compile --out '/tmp/{size} rejection.js'" \
          --cleanup "rm '/tmp/{size} rejection.js'" \
          "node '/tmp/{size} rejection.js'"

# Create plots_6_7.tex
head -n 24 plot.tex > plots_6_7.tex
cat pcfg-pac.csv | awk '{print $0"," NR-1",COUNT\\\\"}' | sed -e 's/parameter_size,.,.*\\\\/parameter_size,length,count\\\\/g' | sed -e "s/COUNT/$hyperfine_runs/g" >> plots_6_7.tex
tail -n 47 plot.tex >> plots_6_7.tex
pdflatex plots_6_7.tex
