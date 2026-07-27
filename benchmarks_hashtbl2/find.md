| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `find hashtbl` | 173.3 ± 2.4 | 170.5 | 179.1 | 1.00 |
| `find hashtbl2` | 188.8 ± 2.2 | 185.2 | 193.2 | 1.09 ± 0.02 |

<!-- SIZE=1023 FIND=150_000 REPLACE=0 ITERATIONS=20 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1023 FIND=150_000 REPLACE=0 ITERATIONS=20 IMPL={impl}       FUNCTION=find_replace ./hashtbl_vs_hashtbl2.exe"       --command-name "find {impl}" --export-markdown find.md -->
