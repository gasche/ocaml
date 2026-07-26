| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add_remove hashtbl` | 389.0 ± 7.2 | 378.8 | 405.1 | 1.00 |
| `add_remove hashtbl2` | 669.7 ± 7.8 | 662.0 | 682.3 | 1.72 ± 0.04 |

<!-- ADD=1000 REMOVE=1000 ITERATIONS=5_000 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "ADD=1000 REMOVE=1000 ITERATIONS=5_000 IMPL={impl}       FUNCTION=add_remove ./hashtbl_vs_hashtbl2.exe"       --command-name "add_remove {impl}" --export-markdown add_remove.md -->
