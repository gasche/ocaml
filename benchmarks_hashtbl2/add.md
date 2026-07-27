| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add hashtbl` | 513.0 ± 11.4 | 503.5 | 552.9 | 1.00 |
| `add hashtbl2` | 750.0 ± 6.1 | 741.2 | 765.8 | 1.46 ± 0.03 |

<!-- SIZE=1000 ITERATIONS=5000 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5000 IMPL={impl}       FUNCTION=add ./hashtbl_vs_hashtbl2.exe"       --command-name "add {impl}" --export-markdown add.md -->
