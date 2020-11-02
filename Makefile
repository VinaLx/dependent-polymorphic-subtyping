PROJECT := Declarative

COQ_PROJECT  := _CoqProject
COQ_MAKE     := coq_makefile
COQ_MAKEFILE := CoqMakefile
COQ_DIR := src/proofs

OTT_SOURCES  := src/ott/Language.ott
OTT_COQ_OUTS := ${COQ_DIR}/Language.v ${COQ_DIR}/DKDeclarative.v

OTT_TEX_FLAGS := -tex_show_meta false
TEX_DIR := tex
TEX_SCRIPT_DIR := scripts

OTT_TEX_OUT := ${TEX_DIR}/Language.ott.tex
LATEXMK_SRC := ${TEX_DIR}/Language.tex

all: coq tex

COQ_SOURCES := $(shell \
	find . -name *.v   \
		$(foreach o,$(notdir ${OTT_COQ_OUTS}),-not -name ${o}))

${COQ_PROJECT} : ${OTT_COQ_OUTS} ${COQ_SOURCES}
	@echo "MAKE: Generating _CoqProject"
	@echo "# Generated by Makefile" > $@
	@echo -R ${COQ_DIR} ${PROJECT}  > $@
	@$(foreach f,$^,echo ${f}      >> $@;)

src/proofs/%.v : src/ott/%.ott
	@echo "MAKE: Generating rules for coq by ott"
	@ott -o $@ $^

${COQ_MAKEFILE} : ${COQ_PROJECT} ${COQ_SOURCES} ${OTT_COQ_OUTS}
	@echo MAKE: Generating ${COQ_MAKEFILE}
	@${COQ_MAKE} -f ${COQ_PROJECT} -o $@

${OTT_TEX_OUT} : ${OTT_SOURCES}
	@echo MAKE: Generating latex typeset of rules
	@mkdir -p ${TEX_DIR}
	@ott ${OTT_TEX_FLAGS} -o $@ $^

.PHONY: all ott coq clean

ott: ${OTT_COQ_OUTS}

coq: ott ${COQ_MAKEFILE}
	@echo "MAKE: Compiling coq sources"
	@${MAKE} -f ${COQ_MAKEFILE}

tex: ${OTT_TEX_OUT} ${TEX_SCRIPT_DIR}/*
	@echo "MAKE: Generating pdf file"
	@. ${TEX_SCRIPT_DIR}/tex-transform.sh $< ${LATEXMK_SRC}
	@latexmk -pdf -outdir=tex ${LATEXMK_SRC}

clean:
	@echo "MAKE: Cleaning all generated files"
	@${MAKE} -f ${COQ_MAKEFILE} clean > /dev/null
	@rm ${COQ_PROJECT} ${OTT_COQ_OUTS}
	@cd ${TEX_DIR} && latexmk -c > /dev/null