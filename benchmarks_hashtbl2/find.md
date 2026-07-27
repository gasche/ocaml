| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `find hashtbl` | 177.8 ± 3.6 | 171.3 | 184.1 | 1.00 |
| `find hashtbl2` | 180.7 ± 4.0 | 174.8 | 189.4 | 1.02 ± 0.03 |

<!-- SIZE=1023 FIND=150_000 REPLACE=0 ITERATIONS=20 -->
<!-- hyperfine --warmup 10 --runs 20 -L impl hashtbl,hashtbl2 "SIZE=1023 FIND=150_000 REPLACE=0 ITERATIONS=20 IMPL={impl}       FUNCTION=find_replace ./hashtbl_vs_hashtbl2.exe"       --command-name "find {impl}" --export-markdown find.md -->
