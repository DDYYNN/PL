(*
 * SNU 4190.310 Programming Languages 
 * K-- to SM5 translator skeleton code
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open K
open Sm5
module Translator = struct

        (* default := NUM ADD LETV READ *)
  (* TODO : complete this function  *)
  let rec trans : K.program -> Sm5.command = function
    | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
    | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
    | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))] (* Sm5.Unit ??? *)
    | K.VAR id -> [Sm5.PUSH (Sm5.Id id); Sm5.LOAD]
    | K.ADD (e1, e2) -> trans e1 @ trans e2 @ [Sm5.ADD]
    | K.SUB (e1, e2) -> trans e1 @ trans e2 @ [Sm5.SUB]
    | K.MUL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.MUL]
    | K.DIV (e1, e2) -> trans e1 @ trans e2 @ [Sm5.DIV]
    | K.EQUAL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.EQ]
    | K.LESS (e1, e2) -> trans e1 @ trans e2 @ [Sm5.LESS]
    | K.NOT e -> trans e @ [Sm5.NOT]
    | K.ASSIGN (id, e) -> trans e @ [Sm5.PUSH (Sm5.Id id); Sm5.STORE; Sm5.PUSH (Sm5.Id id); Sm5.LOAD]
    | K.SEQ (e1, e2) -> trans e1 @ [Sm5.POP] @ trans e2
    | K.IF (cond, e1, e2) -> trans cond @ [Sm5.JTR (trans e1, trans e2)] 
    | K.WHILE (cond, e) -> 
                    let loop = K.LETF ("!cond", "@e", K.IF (K.VAR "@e", K.SEQ(e,
                    K.CALLV ("!cond", cond)), K.UNIT), K.CALLV ("!cond", cond))
                    in trans loop
    | K.FOR (id, e1, e2, e3) ->
                    let loop = K.LETV ("@to", e2, K.LETF ("!from", "#", K.IF (K.LESS
                    (K.VAR "@to", K.VAR "#"), K.UNIT, K.SEQ (K.ASSIGN (id, K.VAR
                    "#"), K.SEQ (e3, K.CALLV ("!from", K.ADD (K.VAR "#", K.NUM
                    1))))), K.CALLV ("!from", e1)))
                    in trans loop
    | K.LETV (x, e1, e2) ->
                    trans e1 @ [Sm5.MALLOC; Sm5.BIND x; Sm5.PUSH (Sm5.Id x); Sm5.STORE] @
                    trans e2 @ [Sm5.UNBIND; Sm5.POP]
    | K.LETF (f, x, e1, e2) ->
                    [Sm5.PUSH (Sm5.Fn (x, [Sm5.BIND f] @ trans e1)); Sm5.BIND f]
                    @ trans e2 @ [Sm5.UNBIND; Sm5.POP]
    | K.CALLV (f, e) ->
                    [Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id f)] @ trans
                    e @ [Sm5.MALLOC; Sm5.CALL]
    | K.CALLR (f, y) ->
                    [Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id
                    y); Sm5.LOAD; Sm5.PUSH (Sm5.Id y); Sm5.CALL]
    | K.READ x -> [Sm5.GET; Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.WRITE e ->
                    trans e @ [Sm5.MALLOC; Sm5.BIND "!"; Sm5.PUSH (Sm5.Id "!");
                    Sm5.STORE; Sm5.PUSH (Sm5.Id "!"); Sm5.PUSH (Sm5.Id "!");
                    Sm5.LOAD; Sm5.PUT; Sm5.LOAD; Sm5.UNBIND; Sm5.POP] 
        
end
