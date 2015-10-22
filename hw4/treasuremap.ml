type treasure = StarBox | NameBox of string
type key = Bar | Node of key * key

type map = End of treasure
| Branch of map * map
| Guide of string * map

exception IMPOSSIBLE

let getReady: map -> key list =
        fun map ->
                match map with
                | End treasure ->
                                raise IMPOSSIBLE (* TODO *) 
                | Branch (m1, m2) ->
                                raise IMPOSSIBLE (* TODO *)
                | Guide (string, map) ->
                                raise IMPOSSIBLE (* TODO *)
