| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `filter_map_inplace hashtbl` | 762.9 ± 17.5 | 736.5 | 786.9 | 1.00 |
| `filter_map_inplace hashtbl2` | 878.2 ± 8.5 | 870.4 | 900.1 | 1.15 ± 0.03 |

<!-- SIZE=1000 ITERATIONS=5_000 RATIO=50 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5_000 RATIO=50 IMPL={impl}       FUNCTION=filter_map_inplace ./hashtbl_vs_hashtbl2.exe"       --command-name "filter_map_inplace {impl}" --export-markdown filter_map_inplace.md -->
