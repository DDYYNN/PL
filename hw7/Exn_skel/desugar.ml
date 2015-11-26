(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open Xexp
exception TODO
(* TODO : Implement this function *)
let rec removeExn : xexp -> xexp = fun e ->
        match e with
        | Num _ | Var _ -> e
        | Fn (x, e') -> Fn (x, removeExn e')
        | App (e1, e2) -> App (removeExn e1, removeExn e2)
        | If (e1, e2, e3) -> If (removeExn e1, removeExn e2, removeExn e3)
        | Equal (e1, e2) -> Equal (removeExn e1, removeExn e2)
        | Raise e' -> raise TODO
        | Handle (e1, n, e2) -> raise TODO
        
