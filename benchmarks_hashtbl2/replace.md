| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `replace hashtbl` | 196.3 ± 4.4 | 190.1 | 204.4 | 1.00 |
| `replace hashtbl2` | 204.3 ± 5.8 | 195.1 | 215.6 | 1.04 ± 0.04 |

<!-- SIZE=1023 FIND=0 REPLACE=150_000 ITERATIONS=20 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "SIZE=1023 FIND=0 REPLACE=150_000 ITERATIONS=20 IMPL={impl}       FUNCTION=find_replace ./hashtbl_vs_hashtbl2.exe"       --command-name "replace {impl}" --export-markdown replace.md -->
