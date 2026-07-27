| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `fold hashtbl` | 724.0 ± 52.1 | 681.4 | 857.9 | 1.37 ± 0.20 |
| `fold hashtbl2` | 527.6 ± 67.4 | 476.4 | 639.8 | 1.00 |

<!-- SIZE=1000 ITERATIONS=100_000 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=100_000 IMPL={impl}       FUNCTION=fold ./hashtbl_vs_hashtbl2.exe"       --command-name "fold {impl}" --export-markdown fold.md -->
