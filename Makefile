main:
	xelatex notes

push:
	scp notes.pdf umd:/fs/www/class/fall2015/cmsc631/

.PHONY:
clean:
	rm -rf *.ans *.aux *.log *.out *.pdf *.toc
