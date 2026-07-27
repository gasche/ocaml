| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `add_remove hashtbl` | 398.9 ± 13.0 | 383.7 | 422.5 | 1.00 |
| `add_remove hashtbl2` | 561.9 ± 10.7 | 540.2 | 584.0 | 1.41 ± 0.05 |

<!-- ADD=1000 REMOVE=1000 ITERATIONS=5_000 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "ADD=1000 REMOVE=1000 ITERATIONS=5_000 IMPL={impl}       FUNCTION=add_remove ./hashtbl_vs_hashtbl2.exe"       --command-name "add_remove {impl}" --export-markdown add_remove.md -->
