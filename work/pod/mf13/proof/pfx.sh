#!/bin/zsh
cd /Users/mike/dev/ctrl/work/pod/mf13/proof
export OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 OPENBLAS_NUM_THREADS=1
exec uv run -q --with numpy --with scipy --with cvxpy --with clarabel --with mpmath --with cma python "$@"
