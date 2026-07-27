| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add_remove hashtbl` | 394.5 ± 12.0 | 383.2 | 421.5 | 1.00 |
| `add_remove hashtbl2` | 487.3 ± 9.5 | 474.6 | 509.3 | 1.24 ± 0.04 |

<!-- ADD=1000 REMOVE=1000 ITERATIONS=5_000 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "ADD=1000 REMOVE=1000 ITERATIONS=5_000 IMPL={impl}       FUNCTION=add_remove ./hashtbl_vs_hashtbl2.exe"       --command-name "add_remove {impl}" --export-markdown add_remove.md -->
