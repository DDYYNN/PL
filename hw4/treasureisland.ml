type key = Bar | Node of key * key
type treasure = StarBox | NameBox of string
type map = End of treasure | Guide of string * map | Branch of map * map
type ty = TVar of int | Default | TPair of ty * ty
type env = E of (string -> ty)
type rule = R of (ty -> ty)
exception IMPOSSIBLE
exception NOKEY

let bind (E env) name ty = E (fun x -> if x = name then ty else env x)
let emptyenv = E (fun x -> raise NOKEY)
let exist2 (E env) name = try let _ = env name in true with NOKEY -> false
let lookup (E env) name = env name

let emptyrule = R (fun x -> x)

let envp = ref emptyenv
let cnt = ref 0

let newt() = cnt := !cnt + 1; TVar !cnt
let push (name, ty) = if exist2 !envp name then () else envp := bind !envp name ty
let find name = lookup !envp name
let exist name = exist2 !envp name
let ( @@ ) g f = fun x -> g (f x)

let rec occurs: ty -> ty -> bool =
        fun t1 t2 ->
                match t1 with
                | Default -> false
                | TVar _ -> t1=t2
                | TPair (a, b) -> (occurs a t2) || (occurs b t2)

let rec unify: ty -> ty -> rule =
        fun t1 t2 ->
                let subst: int -> ty -> rule =
                        fun x tau ->
                                let rec s: ty -> ty =
                                        fun t ->
                                                match t with
                                                | TVar y -> if y = x then tau else t (* t=x??*)
                                                | TPair (t1, t2) -> TPair (s t1, s t2) 
                                                | Default -> Default in
                                        R s in
                match (t1, t2) with
                | (TVar x, _) ->
                                if t1=t2 then emptyrule
                                else if not (occurs t1 t2) then subst x t2
                                else raise IMPOSSIBLE
                | (TPair (a, b), TPair (c, d)) ->
                                let R r1 = unify a b in
                                let R r2 = unify (r1 c) (r1 d) in
                                R (r2 @@ r1)
                | (_, TVar _) -> unify t2 t1
                | _ -> if t1=t2 then emptyrule else raise IMPOSSIBLE

let rec matching : map -> ty * rule =
        fun map ->
                match map with
                | End StarBox -> (Default, emptyrule)
                | End (NameBox name) ->
                                if exist name then
                                        (find name, emptyrule)
                                else   
                                        (push (name, newt());
                                        (find name, emptyrule))
                | Guide (name, map') ->
                                if not (exist name) then
                                        push (name, newt());
                                let (tvalue, R rule') = matching map' in
                                (TPair (rule' (find name), tvalue), R rule')
                | Branch (m1, m2) ->
                                let (tv1, R r1) = matching m1 in
                                let E e = !envp in
                                envp := E (r1 @@ e);
                                let (tv2, R r2) = matching m2 in
                                let temp = newt() in
                                let R rule = unify (TPair (tv2, temp)) (r2 tv1) in
                                (rule temp, R (rule @@ (r2 @@ r1)))

let rec map2key: map -> rule -> key list =
        fun map (R rule) ->
                let rec convert: ty -> key =
                        fun ty ->
                                match ty with
                                | TPair (t1, t2) -> Node (convert t1, convert t2)
                                | TVar _ -> convert (rule ty)
                                | _ -> Bar in
                let rec appending: key list -> key list -> key list =
                        fun l1 l2 ->
                                match l2 with
                                | [] -> l1
                                | h::t ->
                                                if List.exists (fun x -> x = h) l1
                                                then appending l1 t
                                                else (appending (h::l1) t) in
                match map with
                | End StarBox -> [Bar]
                | End (NameBox name) -> [convert (rule (find name))]
                | Guide (name, map') -> map2key map' (R rule)
                | Branch (m1, m2) -> appending (map2key m1 (R rule)) (map2key m2
                (R rule))



let getReady: map -> key list =
        fun map ->
                let (_, rule) = matching map in
                let keys = map2key map rule in
                cnt := 0;
                envp := emptyenv;
                keys

