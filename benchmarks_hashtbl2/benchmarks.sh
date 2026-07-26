make -C .. -j || exit 2

../ocamlopt.opt -nostdlib -I ../stdlib hashtbl_vs_hashtbl2.ml \
   -o hashtbl_vs_hashtbl2.exe || exit 2

run () {
    cmd="hyperfine -L impl hashtbl,hashtbl2 \"$params IMPL={impl} \
      FUNCTION=$bench ./hashtbl_vs_hashtbl2.exe\" \
      --command-name \"$file {impl}\" --export-markdown $file.md"
    echo
    echo
    echo "$cmd"
    eval "$cmd"
    echo >> $file.md
    echo "<!-- $params -->" >> $file.md
    echo "<!-- $cmd -->" >> $file.md
}

bench=add
params="SIZE=1000 ITERATIONS=5000"
file=$bench
run

bench=find_replace
params="SIZE=1023 FIND=150_000 REPLACE=0 ITERATIONS=20"
file=find
run

params="SIZE=1023 FIND=0 REPLACE=150_000 ITERATIONS=20"
file=replace
run

bench=add_remove
params="ADD=1000 REMOVE=1000 ITERATIONS=5_000"
file=$bench
run

bench=fold
params="SIZE=1000 ITERATIONS=100_000"
file=$bench
run

bench=filter_map_inplace
params="SIZE=1000 ITERATIONS=5_000 RATIO=50"
file=$bench
run
