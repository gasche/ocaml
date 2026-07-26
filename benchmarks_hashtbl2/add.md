| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add hashtbl` | 524.5 ± 15.2 | 511.0 | 562.7 | 1.00 |
| `add hashtbl2` | 691.4 ± 13.9 | 680.2 | 720.4 | 1.32 ± 0.05 |

<!-- SIZE=1000 ITERATIONS=5000 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5000 IMPL={impl}       FUNCTION=add ./hashtbl_vs_hashtbl2.exe"       --command-name "add {impl}" --export-markdown add.md -->
