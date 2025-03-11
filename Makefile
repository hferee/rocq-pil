EXTRA_DIR:= doc-config
COQDOCFLAGS:= \
  --toc --toc-depth 3 --html --interpolate \
	-d docs -s --lib-subtitles \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
PUBLIC_URL="https://hferee.github.io/UIML"
SUBDIR_ROOTS := theories
DIRS := . $(shell find $(SUBDIR_ROOTS) -type d)
BUILD_PATTERNS := *.vok *.vos *.glob *.vo
BUILD_FILES := $(foreach DIR,$(DIRS),$(addprefix $(DIR)/,$(BUILD_PATTERNS)))

_: makefile.coq

makefile.coq:
	coq_makefile -f _CoqProject -docroot docs -o $@

-include makefile.coq

clean::
	rm makefile.coq makefile.coq.conf
	rm -f $(BUILD_FILES)
	rm -f extraction/*.ml extraction/*.mli

# OCaml build
#SOURCE_ROOT=extraction
#BUILD_PATTERNS := *.ml *.mli
#SOURCES=$(addprefix $(SOURCE_ROOT)/,$(BUILD_PATTERNS))
#RESULT=extraction/PIL

bin: theories/PIL/extraction.vo bin/pil_cmdline.ml
	dune build


#-include OCamlMakefile

.PHONY: _
