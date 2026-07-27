| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add hashtbl` | 509.6 ± 5.1 | 502.6 | 518.0 | 1.00 |
| `add hashtbl2` | 766.1 ± 4.8 | 756.7 | 773.4 | 1.50 ± 0.02 |

<!-- SIZE=1000 ITERATIONS=5000 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5000 IMPL={impl}       FUNCTION=add ./hashtbl_vs_hashtbl2.exe"       --command-name "add {impl}" --export-markdown add.md -->
