ROOTDIR=..
OCAMLRUN=$(ROOTDIR)/runtime/ocamlrun
STDFLAGS=-nostdlib -I $(ROOTDIR)/stdlib
OCAMLC=$(OCAMLRUN) $(ROOTDIR)/ocamlc $(STDFLAGS)
OCAMLOPT=$(OCAMLRUN) $(ROOTDIR)/ocamlopt $(STDFLAGS)

BENCHS=wrong-int zarith unboxed unboxed_both boxed
BENCH_SIZE ?= 20

run: test.byte test.native
	for bench in $(BENCHS); do\
	  echo -e "\n\ntest.byte $$bench:";\
	  time ./test.byte $$bench $(BENCH_SIZE) 1_000_000;\
	done;\
	for bench in $(BENCHS); do\
	  echo -e "\n\ntest.native $$bench:";\
	  time ./test.native $$bench $(BENCH_SIZE) 10_000_000;\
	done

run-with-overflow:
	$(MAKE) run BENCH_SIZE=22

ZARITH_FLAGS=-ccopt "-I$(ROOTDIR)/runtime -DHAS_GMP -O3 -Wall -Wextra" -cclib -lgmp

test.cmm: test.ml
	$(OCAMLOPT) -c test.ml -dcmm 2>test.cmm

test.byte: test.ml caml_z.c
	$(OCAMLC) -o test.byte -custom $(ZARITH_FLAGS) -linkall caml_z.c test.ml

test.native: test.ml caml_z.c
	$(OCAMLOPT) -o test.native $(ZARITH_FLAGS) caml_z.c test.ml

clean:
	rm -f test.cm* test.o caml_z.o test.byte test.native
