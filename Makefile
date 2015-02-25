all:
	coqc F01_Defs.v F03_Insert_kind.v F04_Env_subst.v F05_Remove_var.v F06_Regularity.v F02_Inference.v 

doc:
	rm -rf html
	mkdir html
	coqdoc -utf8 -g -d html -toc F01_Defs.v F03_Insert_kind.v F04_Env_subst.v F05_Remove_var.v F06_Regularity.v F02_Inference.v 

ssh: doc
	scp html/* sboul434@ssh.eleves.ens-rennes.fr:/home/sboul434/public_html/systemf/

clean:
	rm -f *.vo *.glob *~
