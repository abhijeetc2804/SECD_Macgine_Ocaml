type exp =
  | Var of string
  | Abs of string * exp
  | App of exp * exp
  | Num of int
  | Bool of bool
  | Add of exp * exp
  | Sub of exp * exp
  | Mult of exp * exp
  | Div of exp * exp
  | Lt of exp * exp
  | Gt of exp * exp
  | Eq of exp * exp
  | If of exp * exp * exp
  | Pair of exp * exp
  | Fst of exp
  | Snd of exp
  | Float of float
  | Tuple of exp list
  | Proj of int * exp
  | And of exp * exp
  | Or of exp * exp
  | Not of exp
  | Xor of exp*exp
  | String of string
  | Concat of exp * exp  
;;



type opcode =
  | LOOKUP of string
  | APP
  | MKCLOS of string * opcode list
  | RET
  | CONST of int
  | CONSTB of bool
  | ADD
  | SUB
  | MULT
  | DIV
  | LT
  | GT
  | EQ
  | IF
  | COND of opcode list * opcode list
  | PAIR
  | FST
  | SND 
  | CONSTF of float
  | TUPLE of int  (* int is the size of the tuple *)
  | PROJ of int  (* Projection: int is 0-based index *)
  | CONSTS of string  (* Push a string constant *)
  | CONCAT
  | AND
  | OR
  | NOT
  | XOR 
;;



type value =
  | VNum of int
  | VBool of bool
  | VClosure of string * opcode list * environment
  | VPair of value * value 
  | VFloat of float
  | VTuple of value list 
  | VString of string
and environment = (string * value) list

    

type stack = value list
type control = opcode list
type dump = (stack * environment * control) list
type machine = stack * environment * control * dump



let rec compile = function
  | Var x -> [LOOKUP x]
  | Abs(x, e) -> [MKCLOS(x, compile e @ [RET])]
  | App(e1, e2) -> compile e1 @ compile e2 @ [APP]
  | Num n -> [CONST n]
  | Bool b -> [CONSTB b]
  | Add(e1, e2) -> compile e1 @ compile e2 @ [ADD]
  | Sub(e1, e2) -> compile e1 @ compile e2 @ [SUB]
  | Mult(e1, e2) -> compile e1 @ compile e2 @ [MULT]
  | Div(e1, e2) -> compile e1 @ compile e2 @ [DIV]
  | Lt(e1, e2) -> compile e1 @ compile e2 @ [LT]
  | Gt(e1, e2) -> compile e1 @ compile e2 @ [GT]
  | Eq(e1, e2) -> compile e1 @ compile e2 @ [EQ]
  | If(cond, e1, e2) -> compile cond @ [COND(compile e1, compile e2)]
  | Pair(e1, e2) -> compile e1 @ compile e2 @ [PAIR]
  | Fst e -> compile e @ [FST]
  | Snd e -> compile e @ [SND]   
  | Float f -> [CONSTF f]
  | Tuple exps -> List.flatten (List.map compile exps) @ [TUPLE (List.length exps)]
  | Proj (index, exp) -> compile exp @ [PROJ index]
  | String s -> [CONSTS s]
  | Concat(e1, e2) -> compile e1 @ compile e2 @ [CONCAT]
  | And(e1, e2) -> compile e1 @ compile e2 @ [AND]
  | Or(e1, e2) -> compile e1 @ compile e2 @ [OR]
  | Not e -> compile e @ [NOT]
  | Xor(e1, e2) -> compile e1 @ compile e2 @ [XOR] 
;;



let rec step = function
  | ([], env, [], d) -> ([], env, [], d)  (* Termination condition *)
  | (s, env, LOOKUP x :: c, d) -> 
      (try let v = List.assoc x env in (v :: s, env, c, d)
       with Not_found -> failwith ("!?! Unknown variable: " ^ x ^ " !?!"))
  | (VNum n2 :: VNum n1 :: s, env, ADD :: c, d) -> (VNum (n1 + n2) :: s, env, c, d)
  | (VNum n2 :: VNum n1 :: s, env, SUB :: c, d) -> (VNum (n1 - n2) :: s, env, c, d)
  | (VNum n2 :: VNum n1 :: s, env, MULT :: c, d) -> (VNum (n1 * n2) :: s, env, c, d)
  | (VNum n2 :: VNum n1 :: s, env, DIV :: c, d) -> (VNum (n1 / n2) :: s, env, c, d) 
  | (VNum n2 :: VNum n1 :: s, env, LT :: c, d) -> (VBool (n1 < n2) :: s, env, c, d)
  | (VNum n2 :: VNum n1 :: s, env, GT :: c, d) -> (VBool (n1 > n2) :: s, env, c, d)
  | (VNum n2 :: VNum n1 :: s, env, EQ :: c, d) -> (VBool (n1 = n2) :: s, env, c, d)
  | (s, env, CONST n :: c, d) -> (VNum n :: s, env, c, d)
  | (s, env, CONSTB b :: c, d) -> (VBool b :: s, env, c, d)
  | (s, env, MKCLOS(x, body) :: c, d) -> (VClosure(x, body, env) :: s, env, c, d)
  | (v :: VClosure(x, c1, env') :: s, env, APP :: c, d) -> 
      ([], (x, v) :: env', c1 @ [RET], (s, env, c) :: d)
  | (v :: s, env, RET :: c, (s', env', c') :: d) -> (v :: s', env', c', d)
  | (VBool true :: s, env, COND(c1, _) :: c, d) -> (s, env, c1 @ c, d)
  | (VBool false :: s, env, COND(_, c2) :: c, d) -> (s, env, c2 @ c, d)
  | (v2 :: v1 :: s, env, PAIR :: c, d) -> (VPair(v1, v2) :: s, env, c, d)
  | (VPair(v1, _) :: s, env, FST :: c, d) -> (v1 :: s, env, c, d)
  | (VPair(_, v2) :: s, env, SND :: c, d) -> (v2 :: s, env, c, d)
  | (s, env, CONSTF f :: c, d) -> (VFloat f :: s, env, c, d)
  | (s, env, TUPLE size :: c, d) ->
      let rec accumul n lst acc =
        if n <= 0 then (acc, lst)
        else match lst with
          | [] -> (List.rev acc, [])
          | x::xs -> accumul (n - 1) xs (x::acc)
      in
      let tuple, rest_s = accumul size s [] in
      (VTuple(tuple) :: rest_s, env, c, d)
  | (VTuple(values) :: s, env, PROJ index :: c, d) ->
      (List.nth values index :: s, env, c, d) 
  | (s, env, CONSTS str :: c, d) -> (VString str :: s, env, c, d) 
  | (VString s2 :: VString s1 :: s, env, CONCAT :: c, d) -> (VString (s1 ^ s2) :: s, env, c, d)
  | (VBool b2 :: VBool b1 :: s, env, AND :: c, d) -> (VBool (b1 && b2) :: s, env, c, d)
  | (VBool b2 :: VBool b1 :: s, env, OR :: c, d) -> (VBool (b1 || b2) :: s, env, c, d)
  | (VBool b :: s, env, NOT :: c, d) -> (VBool (not b) :: s, env, c, d)
  | (VBool b2 :: VBool b1 :: s, env, XOR :: c, d) -> (VBool ((b1 || b2) && not (b1 && b2)) :: s, env, c, d) 
  | _ -> failwith "!?! SECD: Error !?!" 
;;



let rec execute_secd machine =
  match machine with
  | (_, _, [], _) -> machine  (* Halt condition: control list is empty *)
  | _ -> execute_secd (step machine)
           
           

let rec string_of_value = function
  | VNum n -> string_of_int n
  | VBool b -> string_of_bool b
  | VClosure _ -> "[CLOSURE]"
  | VPair(v1, v2) -> "(" ^ string_of_value v1 ^ ", " ^ string_of_value v2 ^ ")"
  | VFloat f -> string_of_float f
  | VTuple vs -> "(" ^ String.concat ", " (List.map string_of_value vs) ^ ")"
  | VString s -> "\"" ^ s ^ "\""  
  
                 

let print_result (s, _, _, _) =
  match s with
  | result :: _ -> print_endline ("Result: " ^ string_of_value result)
  | [] -> print_endline "Error: Machine finished without a result"



(* Test cases *)
let test1 = Add(Num 3, Num 2) 
let test2 = If(Bool true, Num 15, Num 10)  
let test3 = App(Abs("x", Add(Var "x",Num 6)), Num 3)
let test4 = If(Bool true,Add(Num 17,Num 1),Num 20) 
let test5 = App(Abs("x", App(Abs("y", Add(Var "x", Var "y")), Num 5)), Num 3);;  (* (\x -> (\y -> x + y) 5) 3 *)
let test6 = Pair(Num 3, Bool true)
let test7 = Abs("x", Add(Var "x", Num 10))
let test8 = Snd(Pair(Bool false, Add(Num 5, Num 5)))
let test9 = If(Lt(Num 1, Num 2), Num 3, Num 4)
let test10 = Eq(Num 5, Add(Num 2, Num 3))
let test11 = If(Eq(Num 10, Add(Num 5, Num 5)), Sub(Num 20, Num 10), Num 0)
let test12 = App(Abs("x", Mult(Var "x", Num 10)), Num 3)
let test13 = Fst(Pair(Add(Num 1, Num 2), Bool true))
let test14 = Snd(Pair(Num 1, If(Bool false, Num 2, Num 3)))
let test15 = If(Gt(Num 5, Num 3), Add(Num 1, Num 2), Sub(Num 5, Num 3))
let test16 = App(Abs("y", Add(Var "y", Mult(Num 2, Num 5))), Num 8)
let test17 = If(Lt(Num 1, Num 2), App(Abs("x", Add(Var "x", Num 3)), Num 4), Num 0)
let test18 = Pair(If(Bool true, Num 10, Num 20), Mult(Num 2, Num 3))
let test19 = Fst(Pair(App(Abs("x", Add(Var "x", Num 5)), Num 10), Bool false))
let test20 = Snd(Pair(Bool true, If(Eq(Num 5, Num 5), Mult(Num 2, Add(Num 3, Num 2)), Sub(Num 10, Num 5)))) 
let test21 = Float 3.14
let test22 = Tuple([Num 1; Float 2.5; Bool true])
let test23 = Proj(0, Tuple([Float 3.14; Float 2.71; Bool false]))
let test24 = And(Bool true, Or(Bool false, Xor(Bool true, Bool false))) 
let test25 = String("Hello there!!!")
let test26 = Concat(String "Hello, ", String "world!") 
let test27 = App(App(Abs("x",Abs("y",Sub(Add(Var "x", Var "y"), Mult(Var "x", Var "y")))),Num 3),Num 2) 
let test28 = Add(Num 3, Var "const_5")
let test29 = If(Var "true_val", String "Global variable is true", String "Global variable is false")
let test30 = App(Var "increment", Num 5)  

(* Function to run a given expression through the SECD machine and print the result *)
let run_and_print_result exp =
  let compiled_opcodes = compile exp in
  let initial_machine_state = ([], [
    ("const_5", VNum 5);
    ("true_val", VBool true);
    ("increment", VClosure("x", [LOOKUP "x"; CONST 1; ADD; RET], []));
  ], compiled_opcodes, []) in
  let final_machine_state = execute_secd initial_machine_state in
  print_result final_machine_state;;

(* let run_and_print_result_with_env exp env =
  let compiled_opcodes = compile exp in
  let initial_machine_state = ([], env, compiled_opcodes, []) in
  let final_machine_state = execute_secd initial_machine_state in
  print_result final_machine_state;; *)



(* Executing and printing results for all test cases *)
let () =
  print_endline "Test Case 1:";
  run_and_print_result test1;

  print_endline "\nTest Case 2:";
  run_and_print_result test2;

  print_endline "\nTest Case 3:";
  run_and_print_result test3;

  print_endline "\nTest Case 4:";
  run_and_print_result test4;

  print_endline "\nTest Case 5:";
  run_and_print_result test5; 

  print_endline "\nTest Case 6:";
  run_and_print_result test6;
  
  print_endline "\nTest Case 7:";
  run_and_print_result test7;
  
  print_endline "\nTest Case 8:";
  run_and_print_result test8;
  
  print_endline "\nTest Case 9:";
  run_and_print_result test9;
  
  print_endline "\nTest Case 10:";
  run_and_print_result test10;
  
  print_endline "\nTest Case 11:";
  run_and_print_result test11;

  print_endline "\nTest Case 12:";
  run_and_print_result test12;

  print_endline "\nTest Case 13:";
  run_and_print_result test13;

  print_endline "\nTest Case 14:";
  run_and_print_result test14;

  print_endline "\nTest Case 15:";
  run_and_print_result test15;

  print_endline "\nTest Case 16:";
  run_and_print_result test16;

  print_endline "\nTest Case 17:";
  run_and_print_result test17;

  print_endline "\nTest Case 18:";
  run_and_print_result test18;

  print_endline "\nTest Case 19:";
  run_and_print_result test19;

  print_endline "\nTest Case 20:";
  run_and_print_result test20;

  print_endline "\nTest Case 21:";
  run_and_print_result test21;
  
  print_endline "\nTest Case 22:";
  run_and_print_result test22;

  print_endline "\nTest Case 23:";
  run_and_print_result test23;
  
  print_endline "\nTest Case 24:";
  run_and_print_result test24;

  print_endline "\nTest Case 25:";
  run_and_print_result test25;
  
  print_endline "\nTest Case 26:";
  run_and_print_result test26;
  
  print_endline "\nTest Case 27:";
  run_and_print_result test27;
  
  print_endline "\nTest Case 28:";
  run_and_print_result test28 ;

  print_endline "\nTest Case 29:";
  run_and_print_result test29;

  print_endline "\nTest Case 30:";
  run_and_print_result test30;  
