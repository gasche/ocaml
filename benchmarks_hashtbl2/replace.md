| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `find_replace hashtbl` | 194.7 ± 5.2 | 187.4 | 203.5 | 1.00 |
| `find_replace hashtbl2` | 226.8 ± 4.0 | 222.3 | 237.6 | 1.17 ± 0.04 |

<!-- SIZE=1023 FIND=0 REPLACE=150_000 ITERATIONS=20 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1023 FIND=0 REPLACE=150_000 ITERATIONS=20 IMPL={impl}       FUNCTION=find_replace ./hashtbl_vs_hashtbl2.exe"       --command-name "find_replace {impl}" --export-markdown replace.md -->
