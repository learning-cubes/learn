# Learning Cubes

Link to the .ova file containing this tool: https://drive.google.com/file/d/1bN5GSb788YajaNAy6Zxwpgi9NW4-uWxL/view?usp=sharing

Run the .ova file as follows:

1. Download and install VirtualBox if you don’t have it already.
2. Open VirtualBox
3. Select File and Import Appliance
4. Select your OVA file in the import box and verify the settings in the center window
5. Make any changes if you need to in that center window
6. Click Import at the bottom.
7. Allow VirtualBox to import the file and configure it for use

Learning Algorithm for learning cubes in linear integer arithmetic using membership, equivalence and inclusion queries
=================================

This file describes how to compile and run the learner.

Prerequisites
-------------

The prototype requires Microsoft Z3 (https://github.com/Z3Prover/z3)
for python and python to run. The easiest way to obtain z3 for python
is with the pip3 installer by typing:

	pip3 install z3-solver

To reproduce the benchmark plot (Fig. 7 in the paper), LaTeX is required and can be installed on debian/ubuntu as follows:

	sudo apt-get install texlive-base texlive-pictures

Reproducing the results from the article
----------------------------------------

In order to generate the file `plots.pdf`, please run:

	./experiments.sh all

The keyword `all` can be replaced by one of the 6 benchmarks below, a second
optional parameter can be used to specify K or D (depending on the considered
benchmark).
All results can be found in the `generated` and compared to the `reference_data`
data folder used in the article.
They can be erased by using the `clean` keyword.
Finally, they can be visualized at any time by issuing:

	pdflatex plots.tex
	evince plots.pdf

As large parameter values could take time to evaluate, we recommend evaluating
each benchmark one by one (see list below),
and stop the procedure when too much time is taken.
The list of benchmarks, timeout value and considered tools and parameter values
can be edited in the constants of `experiments.sh`.

Running the prototype
---------------------

To run the prototype, several arguments have to be passed to the python call.

1) Benchmark selection:
We have 6 types of benchmarks available.
    - dia-r (This is K Diagonal Restricted in the paper)
    - dia-u (This is K Diagonal Unrestricted in the paper)
    - big-c (This is K Big Overlapping Cube in the paper)
    - k-cubes (This is K cubes in Z^d in the paper)
    - k-dia (This is K Diagonal in the paper)
    - mondec (This is Example 2 in the paper)

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

    python3 maximal_cubes.py dia-r max-o 50
         

The prototype outputs the total time needed to solve the benchmark at the end.

# Running mondec

We compared our tool against mondec_1 from (https://www.microsoft.com/en-us/research/wp-content/uploads/2017/04/mondec.pdf).

The benchmarks can be run in a similar way except there is no tool selection.
We have 1) Benchmark 2) Parameter K 3) Parameter D

On Linux, for instance, the prototype can be started using the command

	python3 mondec.py dia-r 50

