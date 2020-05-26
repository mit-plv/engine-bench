#!/usr/bin/env bash

# Pass this script a list of file names, and it'll print the relevant
# lines for README.md to display things
#echo intros_n_let.v do_n_pose.v let_n_uconstr.v let_n_ltac2.v

stems="$@"
stems="$(echo "$stems" | tr ' ' '\n' | sed 's/\.v$//g' | tr '\n' ' ')"
extra_bar=""
extra_bar_space=""
if [ "$(echo $stems | wc -w)" -eq 1 ]; then extra_bar="|"; extra_bar_space=" |"; fi
echo $stems | sed 's/ /, /g; s|\([^, ]\+\)|[`coq/PerformanceExperiments/\1.v`](./coq/PerformanceExperiments/\1.v)|g; s/, \([^, ]\+\)$/, and \1/g'
echo
echo -n '  '
echo $stems | sed 's/ / | /g; s/$/'"$extra_bar_space"'/g'
echo -n '  '
echo $stems | sed 's/[^ ]\+/--/g; s/ /|/g; s/$/'"$extra_bar"'/g'
echo -n '  '
echo $stems | sed 's/_/-/g; s/ / | /g; s,\([^ |]\+\),<img src="https://mit-plv.github.io/engine-bench/coq/\1.svg" height=100px />,g; s/$/'"$extra_bar_space"'/g'
