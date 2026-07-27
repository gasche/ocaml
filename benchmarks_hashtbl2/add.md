| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add hashtbl` | 526.4 ± 34.0 | 470.8 | 605.4 | 1.00 |
| `add hashtbl2` | 574.9 ± 12.9 | 554.1 | 604.3 | 1.09 ± 0.07 |

<!-- SIZE=1000 ITERATIONS=5000 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5000 IMPL={impl}       FUNCTION=add ./hashtbl_vs_hashtbl2.exe"       --command-name "add {impl}" --export-markdown add.md -->
