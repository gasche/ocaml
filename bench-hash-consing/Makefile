OCAMLC=ocamlc

all: bench_bdd.byte bench_lambda.byte

clean:
	rm -f *.cmo *.cmi

hashcons.cmi: hashcons.mli
	$(OCAMLC) -c hashcons.mli

hashcons.cmo: hashcons.ml hashcons.cmi
	$(OCAMLC) -c hashcons.ml

bench_bdd.byte: hashcons.cmo bench_bdd.ml
	$(OCAMLC) hashcons.cmo bench_bdd.ml -o bench_bdd.byte

bench_lambda.byte: hashcons.cmo bench_lambda.ml
	$(OCAMLC) hashcons.cmo bench_lambda.ml -o bench_lambda.byte


