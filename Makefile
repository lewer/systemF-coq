all: compile doc

compile:
	coqc F00_docindex.v F01_Defs.v F03_Insert_kind.v F04_Remove_var.v F05_Env_subst.v F06_Regularity.v F02_Inference.v F07_Normalisation.v

doc:
	rm -rf html
	mkdir html
	coqdoc -utf8 -d html --index coqindex -s -toc F00_docindex.v F01_Defs.v F03_Insert_kind.v F04_Remove_var.v F05_Env_subst.v F06_Regularity.v F02_Inference.v F07_Normalisation.v
	cp -f assets/* html

ssh: doc
	scp html/* sboul434@ssh.eleves.ens-rennes.fr:/home/sboul434/public_html/systemf/

clean:
	rm -f *.vo *.glob *~
