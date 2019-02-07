OCAML_OPTIONS = \
-I /home/tnguyen/Dropbox/git/common_code/ \
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/ext/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/src/frontc/\
-I /home/tnguyen/Src/Devel/CIL/cil-1.7.3/_build/ocamlutil/\

OCAMLC =    ocamlfind  ocamlc   $(OCAML_OPTIONS)
OCAMLOPT =  ocamlfind ocamlopt $(OCAML_OPTIONS)
OCAMLDEP =  ocamldep $(OCAML_OPTIONS)
OCAMLLEX =  ocamllex 

all: vu_common cil_common

%.cmx: %.ml 
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
	$(OCAMLOPT) -c $*.ml
	@$(OCAMLDEP) $*.ml > $*.d 

%.cmi: %.mli
	$(OCAMLC) -c -g $*.mli


# NOTE: Module order is important!  OCaml module dependencies cannot
# be cyclic, and the order presented must respect the dependency order.

VU_COMMON_MODULES = \
	vu_common.cmo \

vu_common: $(VU_COMMON_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa $^

# nums.cmxa

CIL_COMMON_MODULES = \
	cil_common.cmo \

cil_common: $(CIL_COMMON_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^

# dependencies
ALL_MODULES =  $(MAIN_MODULES) 

-include $(ALL_MODULES:.cmo=.d)

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o vu_common cil_common
