#**************************************************************************
#*                                                                        *
#*                                 OCaml                                  *
#*                                                                        *
#*            Xavier Leroy, projet Cristal, INRIA Rocquencourt            *
#*                                                                        *
#*   Copyright 1999 Institut National de Recherche en Informatique et     *
#*     en Automatique.                                                    *
#*                                                                        *
#*   All rights reserved.  This file is distributed under the terms of    *
#*   the GNU Lesser General Public License version 2.1, with the          *
#*   special exception on linking described in the file LICENSE.          *
#*                                                                        *
#**************************************************************************

ROOTDIR = ..

include $(ROOTDIR)/Makefile.common
include $(ROOTDIR)/Makefile.best_binaries

DYNLINKDIR=$(ROOTDIR)/otherlibs/dynlink
UNIXDIR=$(ROOTDIR)/otherlibs/$(UNIXLIB)
CAMLRUN ?= $(ROOTDIR)/boot/ocamlrun
CAMLYACC ?= $(ROOTDIR)/yacc/ocamlyacc$(EXE)

CAMLC=$(BEST_OCAMLC) -g -nostdlib -I $(ROOTDIR)/stdlib
COMPFLAGS=$(INCLUDES) -absname -w +a-4-9-41-42-44-45-48 -warn-error A \
          -safe-string -strict-sequence -strict-formats
LINKFLAGS=-linkall -I $(UNIXDIR) -I $(DYNLINKDIR)
YACCFLAGS=
CAMLLEX=$(BEST_OCAMLLEX)
CAMLDEP=$(BEST_OCAMLDEP)
DEPFLAGS=-slash -map ocamldebug_map.mli
DEPINCLUDES=$(INCLUDES)

DIRECTORIES=$(UNIXDIR) $(DYNLINKDIR) $(addprefix $(ROOTDIR)/,\
  utils parsing typing bytecomp toplevel driver file_formats lambda)

INCLUDES=$(addprefix -I ,$(DIRECTORIES))

compiler_modules := $(ROOTDIR)/toplevel/genprintval

debugger_modules := \
  ocamldebug_int64ops ocamldebug_primitives ocamldebug_unix_tools \
  ocamldebug_config ocamldebug_parameters ocamldebug_lexer \
  ocamldebug_input_handling ocamldebug_question ocamldebug_debugcom \
  ocamldebug_exec ocamldebug_source ocamldebug_pos ocamldebug_checkpoints \
  ocamldebug_events ocamldebug_program_loading ocamldebug_symbols \
  ocamldebug_breakpoints ocamldebug_trap_barrier ocamldebug_history \
  ocamldebug_printval ocamldebug_show_source ocamldebug_time_travel \
  ocamldebug_program_management ocamldebug_frames ocamldebug_eval \
  ocamldebug_show_information ocamldebug_loadprinter  \
  ocamldebug_parser ocamldebug_command_line ocamldebug_main

all_modules := $(compiler_modules) $(debugger_modules)

all_objects := $(addsuffix .cmo,$(all_modules))

libraries = $(ROOTDIR)/compilerlibs/ocamlcommon.cma \
  $(UNIXDIR)/unix.cma $(DYNLINKDIR)/dynlink.cma

all: ocamldebug$(EXE)

ocamldebug$(EXE): $(libraries) $(all_objects)
	$(CAMLC) $(LINKFLAGS) -o $@ -linkall $^

install:
	$(INSTALL_PROG) ocamldebug$(EXE) "$(INSTALL_BINDIR)/ocamldebug$(EXE)"

clean::
	rm -f ocamldebug ocamldebug.exe
	rm -f *.cmo *.cmi

.SUFFIXES:
.SUFFIXES: .ml .cmo .mli .cmi

ocamldebug_map.cmi: ocamldebug_map.mli
	$(CAMLC) -c -no-alias-deps $<

.ml.cmo: ocamldebug_map.cmi
	$(CAMLC) -c $(COMPFLAGS) -open Ocamldebug_map $<

.mli.cmi: ocamldebug_map.cmi
	$(CAMLC) -c $(COMPFLAGS) -open Ocamldebug_map $<

depend: beforedepend
# we need -as-map in the camldep invokation because ocamldebug_map.mli
# is one of the *.mli files; if we don't use -as-map here, it gets
# listed and depends on all other .cmi, which create cyclic
# dependencies.
	$(CAMLDEP) $(DEPFLAGS) $(DEPINCLUDES) -open Ocamldebug_map -as-map *.mli *.ml \
	| sed -e 's,$(UNIXDIR)/,$$(UNIXDIR)/,' > .depend

ocamldebug_lexer.ml: ocamldebug_lexer.mll
	$(CAMLLEX) $(OCAMLLEX_FLAGS) $<
clean::
	rm -f ocamldebug_lexer.ml
beforedepend:: ocamldebug_lexer.ml

ocamldebug_parser.ml ocamldebug_parser.mli: ocamldebug_parser.mly
	$(CAMLYACC) ocamldebug_parser.mly
clean::
	rm -f ocamldebug_parser.ml ocamldebug_parser.mli
beforedepend:: ocamldebug_parser.ml ocamldebug_parser.mli

include .depend
