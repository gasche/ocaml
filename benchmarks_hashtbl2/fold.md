| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `fold hashtbl` | 761.4 ± 79.2 | 701.8 | 878.3 | 1.00 |
| `fold hashtbl2` | 1163.2 ± 57.3 | 1114.7 | 1261.2 | 1.53 ± 0.18 |

<!-- SIZE=1000 ITERATIONS=100_000 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=100_000 IMPL={impl}       FUNCTION=fold ./hashtbl_vs_hashtbl2.exe"       --command-name "fold {impl}" --export-markdown fold.md -->
