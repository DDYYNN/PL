all: run clean

run: commonGrade.cmo treasureisland.cmo
	ocaml commonGrade.cmo treasureisland.cmo hw4_2_grade.ml

commonGrade.cmo:
	ocamlc commonGrade.ml
treasureisland.cmo:
	ocamlc treasureisland.ml

clean:
	rm -rf *.cmo *.cmi a.out
