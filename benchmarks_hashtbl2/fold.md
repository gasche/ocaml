| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `fold hashtbl` | 775.2 ± 68.7 | 705.2 | 876.9 | 1.00 |
| `fold hashtbl2` | 1168.9 ± 73.0 | 1114.4 | 1277.5 | 1.51 ± 0.16 |

<!-- SIZE=1000 ITERATIONS=100_000 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=100_000 IMPL={impl}       FUNCTION=fold ./hashtbl_vs_hashtbl2.exe"       --command-name "fold {impl}" --export-markdown fold.md -->
