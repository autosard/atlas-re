#!/usr/bin/env bash

i=1
for example in SkewHeapST SkewHeap2 SkewHeap3over2 SkewHeapGolden WeightBiased WeightBiasedWC RankBiased RankBiasedWC
do
    echo Running benchmark ${i}/8:
    echo 
    wrapper.sh infer ${example}
    i=$((${i} + 1))
done

