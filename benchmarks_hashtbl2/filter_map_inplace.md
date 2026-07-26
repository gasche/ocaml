| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `filter_map_inplace hashtbl` | 745.6 ± 26.4 | 717.6 | 786.8 | 1.00 |
| `filter_map_inplace hashtbl2` | 935.0 ± 31.5 | 900.4 | 1016.5 | 1.25 ± 0.06 |

<!-- SIZE=1000 ITERATIONS=5_000 RATIO=50 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=5_000 RATIO=50 IMPL={impl}       FUNCTION=filter_map_inplace ./hashtbl_vs_hashtbl2.exe"       --command-name "filter_map_inplace {impl}" --export-markdown filter_map_inplace.md -->
