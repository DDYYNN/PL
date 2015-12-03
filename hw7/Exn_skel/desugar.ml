(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open Xexp
exception TODO

let kcount = ref 0
let hcount = ref 0

let new_name () =
        let _ = kcount := !kcount + 1 in
        "x_" ^ (string_of_int !kcount)
let new_h () =
        let _ = hcount := !hcount + 1 in
        "h_" ^ (string_of_int !hcount)

let rec alpha_conv exp subs =
        match exp with
        | Num n -> Num n
        | Var x -> (try Var (List.assoc x subs) with Not_found -> Var x)
        | Fn (x, e) ->
                        let x' = new_name () in
                        let subs' = (x, x') :: subs in
                        Fn (x', alpha_conv e subs')
        | App (e1, e2) -> App (alpha_conv e1 subs, alpha_conv e2 subs)
        | If (e1, e2, e3) -> If (alpha_conv e1 subs, alpha_conv e2 subs, alpha_conv e3 subs)
        | Equal (e1, e2) -> Equal (alpha_conv e1 subs, alpha_conv e2 subs)
        | Raise e -> Raise (alpha_conv e subs)
        | Handle (e1, n, e2) -> Handle (alpha_conv e1 subs, n, alpha_conv e2 subs)

let rec cps: xexp -> xexp = 
        let k = new_name () in
        let h = new_h () in function
        | Num n -> Fn (k, Fn (h, App (Var k, Num n)))
        | Var x -> Fn (k, Fn (h, App (Var k, Var x)))
        | Fn (x, e) -> Fn (k, Fn (h, App (Var k, Fn (x, cps e))))
        | App (e1, e2) -> 
                        let f = new_name () in
                        let v = new_name () in
                        Fn (k, Fn (h, App (App (
                               cps e1,
                               Fn (f, App (App (cps e2, Fn (v, App (App (App (Var f, Var v), Var k), Var h))), Var h))),
                               Var h
                        )))
        | If (e1, e2, e3) ->
                        let z = new_name () in
                        let v1 = new_name () in
                        let v2 = new_name () in
                        Fn (k, Fn (h, App (App (cps e1, Fn (z, If (Var z, App (App (cps e2, Fn
                        (v1, App (Var k, Var v1))), Var h), App (App (cps e3, Fn (v2, App
                        (Var k, Var v2))), Var h)))), Var h)))
        | Equal (e1, e2) -> 
                        let v1 = new_name () in
                        let v2 = new_name () in
                        Fn (k, Fn (h, App (App (cps e1, Fn (v1, App (App (cps e2, Fn (v2, App
                        (Var k, Equal (Var v1, Var v2)))), Var h))), Var h)))
        | Raise e -> Fn (k, Fn (h, App (App (cps e, Var h), Var h)))
        | Handle (e1, n, e2) -> 
                        let v1 = new_name () in
                        Fn (k, Fn (h, App (App
                        (cps e1, Var k), Fn (v1, If (Equal (Num n, Var v1), App
                        (App (cps e2, Var k), Var h), App (Var h, Var v1)))
                        )))

(* TODO : Implement this function *)
let removeExn : xexp -> xexp = fun e ->
        let v = new_name () in
        let h = "BasicHandler" in
        App (App (cps (alpha_conv e []), Fn (v, Var v)), Fn (h, Num 201511))
