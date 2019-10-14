#!/usr/bin/env bash

res_raw="bm_results_raw"
res="bm_results"

make clean
make

mv $res_raw ${res_raw}_old
for i in $(ls ../benchmarks/*.gz)
do
    echo $i >> $res_raw
    predictor $i >> $res_raw
done;

mv $res ${res}_old
grep "openend: MISPRED_PER_1K_INST" $res_raw | grep -oP "[0-9]+\.[0-9]+" > $res
