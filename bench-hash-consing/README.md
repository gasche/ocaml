
# Quick and dirty benchmarks for the Hashcons library

Compile with
   ```
    dune build
   ```

For each program,
- the integer parameter can be used to increase/decrease the
  running time;
- command-line option `-v` prints statistics over the hash-consing
  table before exiting the program.

## BDD benchmark

  Run either of these two commands:
  ```
    ./bench_bdd.exe -de-bruijn 350

    ./bench_bdd.exe -pigeon 11

    ```

## Lambda-calculus benchmark

  Run this command:
    ```
    ./bench_lambda 5
    ```
