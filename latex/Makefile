all: Makefile *.tex 
	for i in *.tex; do pdflatex $$i;done

quick:
	pdflatex main	

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.rel main.pdf *.zip *.bak

.PHONY: all clean
