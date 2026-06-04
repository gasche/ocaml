# Quick and dirty benchmarks for the Hashcons library

Compile with

```
make
```

For each program,
- the integer parameter can be used to increase/decrease the
  running time;
- command-line option `-v` prints statistics over the hash-consing
  table before exiting the program.

## BDD benchmark

Run either of these two commands:

```
./bench_bdd.byte -de-bruijn 350
./bench_bdd.byte -pigeon 11
```

## Lambda-calculus benchmark

Run this command:

```
./bench_lambda.byte 5
```

## Running from the compiler repository

```
make OCAMLC="../runtime/ocamlrun ../ocamlc -nostdlib -I ../stdlib"
../runtime/ocamlrun ./bench_bdd.byte -de-bruijn 350
../runtime/ocamlrun ./bench_bdd.byte -pigeon 11
../runtime/ocamlrun ./bench_lambda.byte 5
```
