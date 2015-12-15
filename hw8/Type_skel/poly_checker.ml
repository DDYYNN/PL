(*
 * SNU 4190.310 Programming Languages 2015 Fall
 * Type Checker Skeleton
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  | TEqual of var
  | TWrite of var
  (* Modify, or add more if needed *)

type typ_scheme =
  | SimpleTyp of typ 
  | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TEqual v | TWrite v | TVar v -> [v] 

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let rec is_equal: typ -> var list = fun t ->
        match t with
        | TPair (t1, t2) -> union_ftv (is_equal t1) (is_equal t2)
        | TLoc t -> is_equal t
        | TFun (t1, t2) -> union_ftv (is_equal t1) (is_equal t2)
        | TEqual var -> [var]
        | _ -> []

let rec is_write: typ -> var list = fun t ->
        match t with
        | TPair (t1, t2) -> union_ftv (is_write t1) (is_write t2)
        | TLoc t -> is_write t
        | TFun (t1, t2) -> union_ftv (is_write t1) (is_write t2)
        | TWrite var -> [var]
        | _ -> []

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TEqual x' | TWrite x' | TVar x' -> if (x = x') then t else t' (* TODO *)
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
    let equals = is_equal t in
    let writes = is_write t in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta ->
                if (List.mem alpha writes)
                then (make_subst alpha (TWrite beta) @@ acc_subst)
                else if (List.mem alpha equals)
                then (make_subst alpha (TEqual beta) @@ acc_subst)
                else (make_subst alpha (TVar beta) @@ acc_subst))
        empty_subst alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let rec expansive: M.exp -> bool = function
        | M.CONST _ | M.VAR _ | M.FN (_, _) | M.LET (M.REC (_, _, _), _) -> false
        | M.MALLOC _ -> true
        | M.BANG e -> expansive e
        | M.APP (_, _) -> true
        | M.ASSIGN (e1, e2) -> (expansive e1) || (expansive e2)
        | M.LET (M.VAL (_, e1), e2) -> (expansive e1) || (expansive e2)
        | M.BOP (_, e1, e2) -> (expansive e1) || (expansive e2)
        | M.IF (e1, e2, e3) -> (expansive e1) || (expansive e2) || (expansive e3)
        | M.READ -> false
        | M.WRITE e -> expansive e
        | M.SEQ (e1, e2) -> (expansive e1) || (expansive e2)
        | M.PAIR (e1, e2) -> (expansive e1) || (expansive e2)
        | M.FST e -> expansive e
        | M.SND e -> expansive e

(* check alpha occur in tau *)
let rec occur: var -> typ -> bool = fun v t ->
        match t with
        | TInt | TBool | TString -> false
        | TPair (t1, t2) -> (occur v t1) || (occur v t2)
        | TLoc t' -> occur v t'
        | TFun (t1, t2) -> (occur v t1) || (occur v t2)
        | TEqual var | TWrite var | TVar var -> v = var

(* TODO : Implement unify // Write > Equal > Var *)
let rec unify: (typ * typ) -> subst = fun (t1, t2) ->
        match (t1, t2) with
        | (TInt, TInt) | (TBool, TBool) | (TString, TString) -> empty_subst
        | (TWrite x, TWrite y) | (TVar x, TVar y) | (TEqual x, TEqual y)
        | (TVar x, TWrite y) | (TVar x, TEqual y) | (TEqual x, TWrite y) -> if x = y then empty_subst else make_subst x t2
        | (_, TWrite _) | (_, TEqual _) | (_, TVar _) -> unify (t2, t1)
        | (TFun (tau1, tau2), TFun (tau1', tau2')) ->
                        let s = unify(tau1, tau1') in
                        let s' = unify(s tau2, s tau2') in
                        s' @@ s
        | (TVar v, _) -> if (occur v t2) 
                        then raise (M.TypeError "unify error")
                        else make_subst v t2
        | (TLoc l1, TLoc l2) -> unify (l1, l2)
        | (TEqual x, TLoc l) -> if (occur x t2) then raise (M.TypeError "unify error") else make_subst x t2
        | (TEqual x, TInt) | (TEqual x, TString) | (TEqual x, TBool)
        | (TWrite x, TInt) | (TWrite x, TString) | (TWrite x, TBool) -> make_subst x t2
        | (TPair (tau1, tau2), TPair (tau1', tau2')) ->
                        let s = unify (tau1, tau1') in
                        let s' = unify (s tau2, s tau2') in
                        s' @@ s
        | _ -> raise (M.TypeError "unify error")
         
let rec chkW: (typ_env * M.exp) -> (subst * typ)  = fun (env, e) ->
        match e with
        | M.CONST (M.S _) -> (empty_subst, TString)
        | M.CONST (M.N _) -> (empty_subst, TInt)
        | M.CONST (M.B _) -> (empty_subst, TBool)
        | M.VAR id ->
                        (try
                                let temp = subst_scheme empty_subst (List.assoc id env) in
                                (match temp with
                                | SimpleTyp typ
                                | GenTyp (_, typ) -> (empty_subst, typ))
                        with Not_found -> raise (M.TypeError "Unbound id"))
        | M.FN (id, exp) ->
                        let beta = TVar (new_var()) in
                        let (s1, tau1) = chkW ((id, SimpleTyp beta)::env, exp)
                        in (s1, TFun (s1 beta, tau1))
        | M.APP (e1, e2) ->
                        let (s1, tau1) = chkW (env, e1) in
                        let (s2, tau2) = chkW (subst_env s1 env, e2) in
                        let beta = TVar (new_var()) in
                        let s3 = unify (s2 tau1, TFun (tau2, beta)) in
                        (s3 @@ s2 @@ s1, s3 beta)
        | M.LET (M.VAL (id, e1), e2) ->
                        let (s1, tau1) = chkW (env, e1) in
                        let env' = subst_env s1 env in
                        if (expansive e1)
                            then
                                    let (s2, tau2) = chkW ((id, SimpleTyp tau1)::env', e2) in
                                    (s2 @@ s1, tau2)
                            else
                                    let (s2, tau2) = chkW ((id, generalize env' tau1)::env', e2) in
                                    (s2 @@ s1, tau2)
        | M.LET (M.REC (f, x, e1), e2) -> 
                        let beta = TVar (new_var()) in
                        let (s1, tau1) = chkW ((f, SimpleTyp beta)::env, M.FN (x, e1)) in
                        let s2 = unify (s1 beta, tau1) in 
                        let (s3, tau2) = chkW ((f, (generalize (subst_env s1 env) (s2 tau1)))::(subst_env s1 env), e2) in
                        (s3 @@ s2 @@ s1, tau2)
        | M.IF (e1, e2, e3) -> 
                        let (s1, tau1) = chkW (env, e1) in
                        let s1' = unify (tau1, TBool) in
                        let (s2, tau2) = chkW (subst_env (s1' @@ s1) env, e2) in
                        let (s3, tau3) = chkW (subst_env (s1' @@ s1) env, e3) in
                        let s4 = unify (tau2, tau3) in
                        (s4 @@ s3 @@ s2 @@ s1' @@ s1, tau3)
        | M.BOP (M.ADD, e1, e2)
        | M.BOP (M.SUB, e1, e2) ->
                        let (s1, tau1) = chkW (env, e1) in
                        let (s2, tau2) = chkW (subst_env s1 env, e2) in
                        let s3 = unify (s2 tau1, TInt) in
                        let s4 = unify (s3 tau2, TInt) in
                        (s4 @@ s3 @@ s2 @@ s1, s4 tau2)
        | M.BOP (M.AND, e1, e2)
        | M.BOP (M.OR, e1, e2) ->
                        let (s1, tau1) = chkW (env, e1) in
                        let (s2, tau2) = chkW (subst_env s1 env, e2) in
                        let s3 = unify (s2 tau1, TBool) in
                        let s4 = unify (tau2, TBool) in
                        (s4 @@ s3 @@ s2 @@ s1, s4 tau2)
        | M.BOP (M.EQ, e1, e2) ->
                        let var = new_var() in
                        let (s1, tau1) = chkW (env, e1) in
                        let (s2, tau2) = chkW (subst_env s1 env, e2) in
                        let s3 = unify (tau2, s2 tau1) in
                        let s4 = unify (TEqual var, s3 tau2) in
                        (s4 @@ s3 @@ s2 @@ s1, TBool)
        | M.READ -> (empty_subst, TInt)
        | M.WRITE e -> 
                        let var = TWrite (new_var()) in
                        let (s1, tau1) = chkW (env, e) in
                        let s2 = unify (tau1, var) in
                        (s2 @@ s1, s2 var)
        | M.MALLOC e ->
                        let (s1, tau1) = chkW (env, e) in
                        (s1, TLoc tau1)
        | M.ASSIGN (e1, e2) -> 
                        let (s1, tau1) = chkW (env, e1) in
                        let (s2, tau2) = chkW (subst_env s1 env, e2) in
                        let s3 = unify (s2 tau1, TLoc tau2) in
                        (s3 @@ s2 @@ s1, s3 tau2)
        | M.BANG e -> 
                        let beta = TVar (new_var()) in
                        let (s1, tau1) = chkW (env, e) in
                        let s2 = unify (tau1, TLoc beta) in
                        (s2 @@ s1, s2 beta)
        | M.SEQ (e1, e2) ->
                        let (s1, tau1) = chkW (env, e1) in
                        let (s2, tau2) = chkW (subst_env s1 env, e2) in
                        (s2 @@ s1, tau2)
        | M.PAIR (e1, e2) ->
                        let (s1, tau1) = chkW (env, e1) in
                        let (s2, tau2) = chkW (subst_env s1 env, e2) in
                        (s2 @@ s1, TPair (s2 tau1, tau2))
        | M.FST e -> 
                        let beta1 = TVar (new_var()) in
                        let beta2 = TVar (new_var()) in
                        let (s1, tau1) = chkW (env, e) in
                        let s2 = unify (tau1, TPair (beta1, beta2)) in
                        (s2 @@ s1, s2 beta1)
        | M.SND e ->
                        let beta1 = TVar (new_var()) in
                        let beta2 = TVar (new_var()) in
                        let (s1, tau1) = chkW (env, e) in
                        let s2 = unify (tau1, TPair (beta1, beta2)) in
                        (s2 @@ s1, s2 beta2)

let rec change: typ -> M.typ = fun typ ->
        match typ with
        | TInt -> M.TyInt
        | TString -> M.TyString
        | TBool -> M.TyBool
        | TLoc typ -> M.TyLoc (change typ)
        | TPair (typ1, typ2) -> M.TyPair (change typ1, change typ2)
        | _ -> raise (M.TypeError "Type error")

(* TODO : Implement this function *)
let check : M.exp -> M.typ = fun e ->
        let (_, typ) = (chkW ([], e)) in
        change typ
