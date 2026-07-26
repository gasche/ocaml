| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `find_replace hashtbl` | 175.7 ± 2.9 | 171.0 | 181.9 | 1.00 |
| `find_replace hashtbl2` | 186.7 ± 2.6 | 182.8 | 191.0 | 1.06 ± 0.02 |

<!-- SIZE=1023 FIND=150_000 REPLACE=0 ITERATIONS=20 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1023 FIND=150_000 REPLACE=0 ITERATIONS=20 IMPL={impl}       FUNCTION=find_replace ./hashtbl_vs_hashtbl2.exe"       --command-name "find_replace {impl}" --export-markdown find.md -->
