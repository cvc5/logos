MAIN := smt-model-definitions
PDF := $(MAIN).pdf
TEX := $(MAIN).tex
LATEX := pdflatex
LATEXFLAGS := -interaction=nonstopmode -halt-on-error

# The built PDF is committed, so it has to be a function of the source alone:
# without this, pdflatex stamps the current time into /CreationDate and every
# rebuild is a diff of a document nobody edited. Override on the command line
# to date a build for real.
SOURCE_DATE_EPOCH ?= 0
export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE = 1

.PHONY: all pdf clean distclean

all: pdf

pdf: $(PDF)

# The document cross-references its figures, so one pass is not enough: the
# first writes the .aux the later ones read. Rerun until LaTeX stops asking,
# capped so that a document that never settles fails rather than loops.
$(PDF): $(TEX)
	$(LATEX) $(LATEXFLAGS) $(TEX)
	@n=0; \
	while grep -Eq 'Rerun to get|Rerun LaTeX|undefined references' $(MAIN).log; do \
	  n=$$((n + 1)); \
	  if [ $$n -gt 3 ]; then \
	    echo "docs/Makefile: $(TEX) still needs another pass after 4; giving up." >&2; \
	    exit 1; \
	  fi; \
	  echo "==> rerunning $(LATEX) (pass $$((n + 1)))"; \
	  $(LATEX) $(LATEXFLAGS) $(TEX); \
	done

clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).toc \
	      $(MAIN).fls $(MAIN).fdb_latexmk $(MAIN).synctex.gz

distclean: clean
	rm -f $(PDF)
