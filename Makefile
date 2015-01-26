all:
	rm -rf ./html/*
	coqc systemf.v
	coqdoc -utf8 -g --no-index -d html systemf.v
	scp html/systemf.html sboul434@ssh.eleves.ens-rennes.fr:/home/sboul434/public_html/systemf/index.html
