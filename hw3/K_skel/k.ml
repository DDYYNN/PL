(*
 * SNU 4190.310 Programming Languages 2015 Fall
 *  K- Interpreter Skeleton Code
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v 
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) = 
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp            (* sequence *)
  | IF of exp * exp * exp       (* if-then-else *)
  | WHILE of exp * exp          (* while loop *)
  | LETV of id * exp * exp      (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list      (* call by value *)
  | CALLR of id * id list       (* call by referenece *)
  | RECORD of (id * exp) list   (* record construction *)
  | FIELD of exp * id           (* access record field *)
  | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp            (* sequence *)
  | IF of exp * exp * exp       (* if-then-else *)
  | WHILE of exp * exp          (* while loop *)
  | LETV of id * exp * exp      (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list      (* call by value *)
  | CALLR of id * id list       (* call by referenece *)
  | RECORD of (id * exp) list   (* record construction *)
  | FIELD of exp * id           (* access record field *)
  | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp

  type program = exp

  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int in value_int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool in value_bool")

  let value_unit v =
      match v with
      | Unit -> ()
      | _ -> raise (Error "TypeError : not unit in value_unit")

  let value_record v =
      match v with
      | Record r -> r
      | _ -> raise (Error "TypeError : not record in value_record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr in lookup_loc")) 
    with Env.Not_bound -> raise (Error "Unbound in lookup_loc")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc in lookup_proc") 
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound in lookup_proc")

  let rec eval mem env e =
    match e with
    | READ x -> (* get int from stdin *)
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e -> (* print int on stdout *)
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    | LETV (x, e1, e2) -> (*store e1 as x in memory and bind at environment *)
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | LETF (id, id_list, e1, e2) ->
    	let env' = Env.bind env id (Proc (id_list, e1, env)) in
	eval mem env' e2
    | ASSIGN (x, e) -> (* change value x in memory to eval e *)
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)
    | ASSIGNF (e1, x, e2) ->
    	let (v, m') = eval mem env e1 in
	let r = value_record v in
	let (v', m'') = eval m' env e2 in
	let l = r x in
	(v', Mem.store m'' l v')
    | NUM i -> (Num i, mem)
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | UNIT -> (Unit, mem)
    | VAR id ->
	let l = lookup_env_loc env id in
	((Mem.load mem l),mem)
    | ADD (e1, e2) ->
                    let (v1, mem') = eval mem env e1 in
                    let (v2, mem'') = eval mem' env e2 in
                    (Num ((value_int v1)+(value_int v2)), mem'')
    | SUB (e1, e2) ->
                    let (v1,mem') = eval mem env e1 in
                    let (v2, mem'') = eval mem' env e2 in
                    (Num((value_int v1) - (value_int v2)), mem'')
    | MUL (e1, e2) ->
                    let (v1,mem') = eval mem env e1 in
                    let (v2, mem'') = eval mem' env e2 in
                    (Num ((value_int v1) * (value_int v2)), mem'')
    | DIV (e1, e2) ->
                    let (v1,mem') = eval mem env e1 in
                    let (v2, mem'') = eval mem' env e2 in
                    (Num ((value_int v1) / (value_int v2)), mem'')
    | EQUAL (e1, e2) ->
                    let (v1, mem') = eval mem env e1 in
                    let (v2, mem'') = eval mem' env e2 in
		    (match (v1, v2) with
		    | (Num i1, Num i2) -> (Bool (i1=i2), mem'')
		    | (Bool b1, Bool b2) -> (Bool (b1=b2), mem'')
		    | (Unit, Unit) -> (Bool true, mem'')
		    | _-> (Bool false, mem''))
    | LESS (e1, e2) ->
                    let (v1, mem') = eval mem env e1 in
                    let (v2, mem'') = eval mem' env e2 in
		    (match (v1, v2) with
		     | (Num i1, Num i2) -> (Bool (i1<i2), mem'')
		     | _ -> raise (Error "TypeError : not int (in LESS)"))
    | NOT e ->
                    let (v, mem') = eval mem env e in
		    (Bool (not (value_bool v)), mem')
    | IF (cond, e1, e2) ->
                    let (con, mem') = eval mem env cond in
		    if (value_bool con) then eval mem' env e1
		    else eval mem' env e2
    | WHILE (cond, e) ->
                    let (c, mem') = eval mem env cond in
                    let (_, mem1) = eval mem' env e in
		    if (value_bool c) then eval mem1 env (WHILE (cond, e))
		    else (Unit, mem')
    | RECORD li ->
    	(match li with
	 | [] -> (Unit, mem)
	 | _ ->
	 	let bind (Record (f)) id l =
			Record (fun x -> if x = id then l else f x) in
		let empty = Record (fun x -> raise (Error "Unbound in record")) in
		let rec loop l m env =
		(match l with
		 | [] -> ([], m)
		 | (id, exp)::t ->
		 	let (v, m') = eval m env exp in
			let (v', m'') = loop t m' env in
			(v::v', m'')) in
		let rec result id_list val_list mem r =
		(match (id_list, val_list) with
		 | ([], []) -> (r, mem)
		 | (id_h::id_t,val_h::val_t) ->
		 	let (l, mem') = Mem.alloc mem in
			let mem'' = Mem.store mem' l val_h in
			let r' = bind r id_h l in
			result id_t val_t mem'' r') in
		let (val_list, mem') = loop li mem env in
		result (fst (List.split li)) val_list mem' empty)
    | FIELD (e, id) ->
    	let (v, m') = eval mem env e in
	let r = value_record v in
	(Mem.load m' (r id), m')
    | CALLV (id, e_list) ->
    	let (id_list, e', env') = lookup_env_proc env id in
	let rec loop env mem e_list = (* exp list -> value list  *)
		(match e_list with
		 | [] -> ([], mem)
		 | h::t ->
		 	let (v, mem') = eval mem env h in
			let (v', mem'') = loop env mem' t in
			(v::v', mem'')) in
	let rec loop2 val_list id_list env mem =
		(match (val_list, id_list) with
		 | ([], []) -> (env, mem)
		 | ([], h::t) -> raise (Error "InvalidArg in CALLV")
		 | (h::t, []) -> raise (Error "InvalidArg in CALLV")
		 | (val_h::val_t,id_h::id_t) ->
			let (l, mem') = Mem.alloc mem in
			let env' = Env.bind env id_h (Addr l) in
			let mem'' = Mem.store mem' l val_h in
			loop2 val_t id_t env' mem'') in
	let (val_list, mem') = loop env mem e_list in
	let (env_r, mem_r) = loop2 val_list id_list env' mem' in
	eval mem_r (Env.bind env_r id (Proc (id_list, e', env'))) e'
    | CALLR (id, id_list) ->
    	let (ref_list, e, env') = lookup_env_proc env id in
	let rec loop env' ref_list id_list =
		(match (ref_list, id_list) with
		 | ([], []) -> env'
		 | ([], h::t) -> raise (Error "InvalidArg")
		 | (h::t, []) -> raise (Error "InvalidArg")
		 | (ref_h::ref_t,id_h::id_t) ->
		 	loop (Env.bind env' ref_h (Addr (lookup_env_loc env id_h))) ref_t id_t) in
	let env_r = loop env' ref_list id_list in
    	eval mem (Env.bind env_r id (Proc (ref_list, e, env'))) e
    | SEQ (e1, e2) ->
    	let (_, mem') = eval mem env e1 in
	let (v2, mem'') = eval mem' env e2 in
	(v2, mem'')

  let run (mem, env, pgm) = 
    let (v, _ ) = eval mem env pgm in
    v
end
