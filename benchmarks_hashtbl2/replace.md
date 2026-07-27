| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `replace hashtbl` | 193.6 ± 2.8 | 187.5 | 199.0 | 1.00 |
| `replace hashtbl2` | 221.3 ± 4.2 | 213.3 | 226.7 | 1.14 ± 0.03 |

<!-- SIZE=1023 FIND=0 REPLACE=150_000 ITERATIONS=20 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1023 FIND=0 REPLACE=150_000 ITERATIONS=20 IMPL={impl}       FUNCTION=find_replace ./hashtbl_vs_hashtbl2.exe"       --command-name "replace {impl}" --export-markdown replace.md -->
