#!/bin/bash

# This file generates the data for the plots of figure 7 of the article

# Official parameters (K for K-parameterized experiments, D for dimension parameterized
# experiments
KPARAMS="50 100 150 200 250 300 350 400 450 500"
DPARAMS="3 4 5 10 50 100 200"

# 5 min
TIMEOUT=300

# dia-r (This is K Diagonal Restricted in the paper)
# dia-u (This is K Diagonal Unrestricted in the paper)
# big-c (This is K Big Overlapping Cube in the paper)
# k-cubes (This is K cubes in Z^d in the paper)
# k-dia (This is K Diagonal in the paper)
# mondec (This is Example 2 in the paper)
BENCHMARKS="dia-r dia-u big-c k-cubes k-dia mondec"

TOOLS="overshoot-u overshoot-b max-u max-b max-o mondec"

parseout() {
    sed "s/Total time needed: *\(.*\)/\1/; t; d"
}

# Clean the generated data
clean() {
  echo "Cleaning generated data";
  for bench in $BENCHMARKS
  do
    echo "clean $bench"
    cat reference_data/$bench.dat | head -n 2 > generated/$bench.dat
  done
}

# Run experiment and fill generated file
# 1 = benchmark name, 2 = parameter
run_exp() {
    if grep -q "^$2 " generated/$1.dat; then
        echo "  Already done, skipping;"
        return
    fi
    # No Param ? Iterate on all of them
    if [ -z $2 ]; then
        if [ "$1" = "k-cubes" ]; then
            params="$DPARAMS"
        else
            params="$KPARAMS"
        fi;
        for p in $params; do
            echo " Instantiate $1 with p=$p"
            run_exp $1 $p
        done;
        return
    fi
    
    # choose between d and k, and the tools to iterate on
    d=2
    k=10
    if [ "$1" = "mondec" ]; then
        tools="max-o mondec"
    else
        tools="$TOOLS"
    fi

    # Only k-cubes has d as the parameter
    if [ "$1" = "k-cubes" ]; then
        d="$2"
    else
        k="$2"
    fi

    
    out="$2"
    for tool in $tools; do
        echo -n "   Running $tool on $1($k,$d) ..."
        res=$(run_tool $tool $1 $k $d | parseout)
        echo "done: ${res}s"
        out="$out     $res"
    done
    echo "$out" >> generated/$1.dat
}


run_tool() {
    if [ "$1" = "mondec" ]; then
        timeout $TIMEOUT python3 ./mondec.py $2 $3 $4
    else
        # Benchmark first
        timeout $TIMEOUT python3 ./maximal_cubes.py $2 $1 $3 $4
    fi
    if [ "$?" -eq 124 ]; then
        echo "Total time needed: $TIMEOUT"
    fi
}

if [ -z "$1" ]; then
    echo "USAGE: $0 [clean|all|$BENCHMARKS] [PARAM]"
    exit 1
elif [ "$1" = "clean" ]; then
   clean
elif [ "$1" = "all" ]; then
    for bench in $BENCHMARKS; do
        run_exp $bench $2
    done
else
    run_exp $1 $2
fi
