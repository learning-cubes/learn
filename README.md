# Learning Cubes
Learning Algorithm for learning cubes in linear integer arithmetic using membership, equivalence and inclusion queries
=================================

This file describes how to compile and run the learner.

Prerequisites
-------------

The prototype requires Microsoft Z3 (https://github.com/Z3Prover/z3)for python and python to run. The easiest way to obtain z3 for python
is with the pip-installer by typing:

        pip-install z3-solver


Running the prototype
---------------------

To run the prototype, several arguments have to be passed to the python call.

1) Benchmark selection:
We have 4 types of benchmarks available.
    - dia-r (This is K Diagonal Restricted in the paper)
    - dia-u (This is K Diagonal Unrestricted in the paper)
    - big-c (This is K Big Overlapping Cube in the paper)
    - k-cubes (This is K cubes in Z^d in the paper)

2) Tool selection:

    The paper has a selection over multiple tools, five of them occur within the paper.
    - overshoot-u (This corresponds to overshoot_unary in the paper)
    - overshoot-b (This corresponds to overshoot_binary in the paper)
    - max-u (This is max_unary in the paper)
    - max-b (This is max_binary  in the paper)
    - max-o (This is max-optimized in the paper)

3) Parameter K:

    All of the benchmarks require a parameter K which usually states how many cubes are in the benchmark.

4) Optional Parameter D:

    The benchmark k-cubes requires another parameter D which corresponds to the dimension d.

On Linux, for instance, the prototype can be started using the command

    ./python maximal_cubes.py dia-r max-o 50
         

The prototype outputs the total time needed to solve the benchmark at the end.

# Running mondec

We compared our tool against mondec1 from (https://www.microsoft.com/en-us/research/wp-content/uploads/2017/04/mondec.pdf).

The benchmarks can be run in a similar way except there is no tool selection.
We have 1) Benchmark 2) Parameter K 3) Parameter D

On Linux, for instance, the prototype can be started using the command

    ./python mondec.py dia-r 50
