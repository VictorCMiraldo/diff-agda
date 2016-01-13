
DIRGUARD=@mkdir -p $(@D)

MAIN_NAME=paper
REFERENCES_NAME=references
LATEXMKOPTS=-pdf -f
TEXT_PARTS_SRC_ROOT=text
TEXT_PARTS_SRC_GENTEX=$(TEXT_PARTS_SRC_ROOT)

MAINTEX=$(TEXT_PARTS_SRC_ROOT)/$(MAIN_NAME).tex
MAINPDF=./$(MAIN_NAME).pdf
REFERENCES=text/$(REFERENCES_NAME).bib
TEXT_PARTS= 

CODE_AGDA_SRC=../
CODE_AGDA_EXCERPTS=excerpts
CODE_AGDA_STY=./agda.sty
CODE_AGDA_STDLIB=/home/victor/.include/agda-stdlib

CODE_AGDA_MODULES=Diffing/Universe/Syntax\
                  Diffing/Universe/Equality\
                  Diffing/Universe/Map\
                  Diffing/Universe/MuUtils\
                  Diffing/Patches/Diff\
                  Diffing/Patches/Residual\
                  Diffing/Patches/Residual/Symmetry\
                  Diffing/Patches/Residual/SymmetryConflict
                  
COMPILER=pdflatex -etex


all: $(MAINPDF)

$(MAINPDF): \
	$(REFERENCES) $(MAINTEX) \
	$(TEXT_PARTS:%=$(TEXT_PARTS_SRC_GENTEX)/%.tex) \
	$(CODE_AGDA_STY) \
	$(CODE_AGDA_MODULES:%=$(CODE_AGDA_EXCERPTS)/%.tex)
	latexmk $(LATEXMKOPTS) $(MAINTEX)
	
$(TEXT_PARTS_SRC_GENTEX)/%.tex: $(TEXT_PARTS_SRC_GENTEX)/%.lhs
	lhs2TeX -o $@ $<
	
force:
	$(COMPILER) $(MAINTEX)

$(CODE_AGDA_EXCERPTS)/%.tex: $(CODE_AGDA_SRC)/%.lagda
	$(DIRGUARD); agda --allow-unsolved-metas -i $(CODE_AGDA_STDLIB) -i $(CODE_AGDA_SRC) \
		--latex-dir=$(CODE_AGDA_EXCERPTS) --latex $<

bib: $(REFERENCES)
	bibtex $(MAIN_NAME).aux

clean:
	rm -f *.log
	rm -f *.ptb
	rm -f *.aux
	rm -f *.toc
	rm -f *.blg
	
cleanall: clean
	rm -f thesis_default.pdf
	rm -f thesis_um.pdf

veryclean: cleanall
	cd code/agda/excerpts && \
	rm -f *.tex

.PHONY: clean veryclean all

