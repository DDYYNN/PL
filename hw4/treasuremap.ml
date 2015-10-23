type treasure = StarBox | NameBox of string
type key = Bar | Node of key * key

type map = End of treasure
| Branch of map * map
| Guide of string * map

exception IMPOSSIBLE
exception NOKEY
exception TODO

let emptyenv = fun x -> raise NOKEY

type env = E of (string -> key)
let bind (E env) name key = E (fun x -> if x = name then key else env x)
let lookup (E env) name = env name

let rec getKey: map -> env -> key =
        fun map env ->
                match map with
                | End StarBox-> Bar
                | End NameBox name -> lookup env name
                | Branch (map1, map2) ->
                                let k1 = getKey map1 env
                                and k2 = getKey map2 env in
                                (match k1 with
                                | Bar -> raise IMPOSSIBLE
                                | Node (a, b) -> if a = k2 then b else raise
                                IMPOSSIBLE)
                                | Guide (name, map') ->
                                                let a = lookup env name
                                                and b = getKey map' env in
                                                Node (a, b)

let getReady: map -> key list =
        fun map -> raise TODO
