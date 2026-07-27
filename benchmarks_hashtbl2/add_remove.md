| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add_remove hashtbl` | 385.2 ± 3.2 | 379.5 | 389.5 | 1.00 |
| `add_remove hashtbl2` | 565.9 ± 7.4 | 553.6 | 577.9 | 1.47 ± 0.02 |

<!-- ADD=1000 REMOVE=1000 ITERATIONS=5_000 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "ADD=1000 REMOVE=1000 ITERATIONS=5_000 IMPL={impl}       FUNCTION=add_remove ./hashtbl_vs_hashtbl2.exe"       --command-name "add_remove {impl}" --export-markdown add_remove.md -->
