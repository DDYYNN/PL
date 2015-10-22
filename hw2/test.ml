type exp = X
		 | ADD of exp * exp
		 | SUB of exp * exp
		 | MUL of exp * exp

let test = ADD (X, (MUL (X, X))) (* x^2 + x *)

let rec make_fun exp arg =
	match exp with
	| X -> arg
	| ADD (e1, e2) -> (make_fun e1 arg) + (make_fun e2 arg)
	| MUL (e1, e2) -> (make_fun e1 arg) * (make_fun e2 arg)
	| SUB (e1, e2) -> (make_fun e1 arg) - (make_fun e2 arg)
