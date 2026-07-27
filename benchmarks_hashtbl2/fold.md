| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `fold hashtbl` | 712.9 ± 51.3 | 676.2 | 856.4 | 1.25 ± 0.16 |
| `fold hashtbl2` | 570.2 ± 58.5 | 538.0 | 696.3 | 1.00 |

<!-- SIZE=1000 ITERATIONS=100_000 -->
<!-- hyperfine -L impl hashtbl,hashtbl2 "SIZE=1000 ITERATIONS=100_000 IMPL={impl}       FUNCTION=fold ./hashtbl_vs_hashtbl2.exe"       --command-name "fold {impl}" --export-markdown fold.md -->
