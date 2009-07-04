#! /bin/bash

# Check again the example files that produced the output files
# currently in the current directy.
#
# Usage: checkAgain.sh
#
# Start from the directory containing the output files of a regression
# test (which should be a sibling directory of BEISPIEL and EXAMPLES).
#
# Uses: sed

. `dirname $0`/parallelTester.lib

# command to be invoked in parallel
_cmd="../py -maxmem 1G -maxtrace 0 -regression"

# number of processors
PMAX=3

(for f in *.reg
do
    # only true if *.reg isn't expanded because there is no matching file
    if [ -f $f ]
    then
        stem=`echo $f | sed -e 's/[.]reg$//'`
        echo ../REGRESSIONS/$stem.inp
    fi
done

for f in *.ref
do
    # only true if *.ref isn't expanded because there is no matching file
    if [ -f $f ]
    then
        stem=`echo $f | sed -e 's/[.]ref$//'`
        echo ../EXAMPLES/$stem.inp
    fi
done

for f in *.out
do
    # only true if *.out isn't expanded because there is no matching file
    if [ -f $f ]
    then
        stem=`echo $f | sed -e 's/[.]out$//'`
        echo ../BEISPIEL/$stem.inp
    fi
done) | dispatchWork
