irrat.glob: irrat.v
	coqc irrat.v

irrat.html: irrat.glob irrat.v
	coqdoc irrat.v
	cp cool-coqdoc.css coqdoc.css

doc: irrat.html
