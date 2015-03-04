all:
	coqc F00_docindex.v F01_Defs.v F03_Insert_kind.v F05_Remove_var.v F04_Env_subst.v F06_Regularity.v F02_Inference.v

doc:
	rm -rf html
	mkdir html
	coqdoc -utf8 -d html --index coqindex -s -toc F00_docindex.v F01_Defs.v F03_Insert_kind.v F05_Remove_var.v F04_Env_subst.v F06_Regularity.v F02_Inference.v
	cp -f assets/* html

coq2html/coq2html:
	ocamllex coq2html/coq2html.mll
	ocamlopt -o coq2html/coq2html str.cmxa coq2html/coq2html.ml

doc2: coq2html/coq2html
	mkdir -p html2
	rm -f html2/*.html
	cp coq2html/coq2html.css coq2html/coq2html.js html2
	coq2html/coq2html -o 'html2/%.html' *.glob F00_docindex.v F01_Defs.v F03_Insert_kind.v F04_Env_subst.v F05_Remove_var.v F06_Regularity.v F02_Inference.v :q

ssh: doc
	scp html/* sboul434@ssh.eleves.ens-rennes.fr:/home/sboul434/public_html/systemf/

clean:
	rm -f *.vo *.glob *~
