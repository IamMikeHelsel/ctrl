#!/bin/zsh
# usage: run.sh script args...   (runs in foreground; call this with block_until_ms=0)
cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
export OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 OPENBLAS_NUM_THREADS=1
exec uv run --with numpy --with scipy --with cma --with mpmath --with clarabel python "$@"
