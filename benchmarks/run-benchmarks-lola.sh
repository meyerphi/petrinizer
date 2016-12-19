#!/bin/bash

benchmarks=( 'service-tech/ibm-soundness' )
extensions=( 'lola' )

properties=( 'safe' 'fin' )

tool='lola'
executable='lola'
options=''

#1 hour
time_soft=$(expr 1 \* 3600)
time_hard=$(expr $time_soft + 60)
#8 gigabyte
mem_soft=$(expr 8 \* 1024 \* 1024)
mem_hard=$(expr $mem_soft + 1024)

for benchmark in ${benchmarks[@]}; do
    benchmark_dir="$benchmark"
    for prop in ${properties[@]}; do
        >$benchmark_dir/$prop-positive-$tool.list
        >$benchmark_dir/$prop-negative-$tool.list
        >$benchmark_dir/$prop-timeout-$tool.list
        >$benchmark_dir/$prop-error-$tool.list
        for ext in ${extensions[@]}; do
            for file in `find $benchmark_dir -name "*.$ext"`; do
                timing="$(date +%s%N)"
                (
                    ulimit -S -t $time_soft
                    ulimit -H -t $time_hard
                    ulimit -S -v $mem_soft
                    ulimit -H -v $mem_hard
                    set -o pipefail;
                    echo $executable $options -f $file.$prop.task $file
                    $executable $options -f $file.$prop.task $file 2>&1 | tee $file.out
                )
                result=$?
                ryes=$(grep "result: yes" $file.out)
                rno=$(grep "result: no" $file.out)
                T=$(($(date +%s%N)-T))
                if [[ -n $ryes ]]; then
                    list='positive'
                elif [[ -n $rno ]]; then
                    list='negative'
                elif [[ result -eq 2 ]]; then
                    list='timeout'
                else
                    list='error'
                fi
                echo $T $file >>$benchmark_dir/$prop-$list-$tool.list
            done
        done
    done
done
