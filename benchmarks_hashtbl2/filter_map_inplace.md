| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `filter_map_inplace hashtbl` | 762.3 ± 21.6 | 719.3 | 805.2 | 1.18 ± 0.06 |
| `filter_map_inplace hashtbl2` | 646.6 ± 27.0 | 596.2 | 691.9 | 1.00 |

<!-- SIZE=1000 ITERATIONS=5_000 RATIO=50 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5_000 RATIO=50 IMPL={impl}       FUNCTION=filter_map_inplace ./hashtbl_vs_hashtbl2.exe"       --command-name "filter_map_inplace {impl}" --export-markdown filter_map_inplace.md -->
