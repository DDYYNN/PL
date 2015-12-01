(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

(* seas.harvard.edu/courses/cs152/2010sp/lectures/lec12.pdf *)
open Xexp

let kcount = ref 0
let hcount = ref 0
let new_name () =
        let _= kcount := !kcount + 1 in
        "x_" ^ (string_of_int !kcount)
let new_h () =
        let _= hcount := !hcount + 1 in
        "h_" ^ (string_of_in !hcount)

let rec cps xexp =
        let k = new_name () in
        let h = new_h () in
        match xexp with
        | Num n -> Fn (k, App (Var k, Num n))
        | Var x -> Fn (k, App (Var k, Var x))
        | Fn (x, e) -> Fn (k, App (Var k, Fn (x, cps e)))
        | App (e1, e2) ->
                        let f = new_name() in
                        let v = new_name() in
                        Fn (k, App (cps e1, Fn (f, App (cps e2, Fn (v, App (App (Var f, Var v), Var k))))))
        | If (e1, e2, e3) -> 
                        let z = new_name() in
                        let v1 = new_name() in
                        let v2 = new_name() in
                        Fn (k, App (cps e1, Fn (z, If (Var z, App (cps e2, Fn (v1, App (Var k, Var v1))), App (cps e3, Fn (v2, App (Var k, Var v2)))))))
        | Equal (e1, e2) ->
                        let f = new_name() in
                        let v = new_name() in
                        Fn (k, App (cps e1, Fn (v, App (cps e2, Fn (v, App (Var k, Equal (Var f, Var v)))))))
        | Raise e' -> raise TODO
        | Handle (e1, n, e2) -> raise TODO 

exception TODO
(* TODO : Implement this function *)
let rec removeExn : xexp -> xexp = fun e ->
        match e with
        | Num _ | Var _ -> e
        | Fn (x, e') -> if is_sugarless e' then e else Fn (x, removeExn e')
        | App (e1, e2) -> App (removeExn e1, removeExn e2)
        | If (e1, e2, e3) -> If (removeExn e1, removeExn e2, removeExn e3)
        | Equal (e1, e2) -> Equal (removeExn e1, removeExn e2)
        | Raise e' -> raise TODO
<<<<<<< HEAD
        | Handle (e1, n, e2) ->
                        If (Equal (e1, Num n), e2, e1)
        
=======
        | Handle (e1, n, e2) -> raise TODO

>>>>>>> cc6e21d86835a461572631789afa227cb09742ab
