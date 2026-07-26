| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `filter_map_inplace hashtbl` | 727.8 ± 21.4 | 698.9 | 766.3 | 1.00 |
| `filter_map_inplace hashtbl2` | 943.8 ± 12.6 | 922.6 | 961.7 | 1.30 ± 0.04 |

<!-- SIZE=1000 ITERATIONS=5_000 RATIO=50 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5_000 RATIO=50 IMPL={impl}       FUNCTION=filter_map_inplace ./hashtbl_vs_hashtbl2.exe"       --command-name "filter_map_inplace {impl}" --export-markdown filter_map_inplace.md -->
