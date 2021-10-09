open Types

let string_of_symbol : sexpr -> string = function
  | Symbol name -> name
  | _ -> failwith "not a symbol"

(*****************************)

let initial_env : env = []


let cons (x:sexpr) (y:sexpr) : sexpr = 
  match y with
  | Atom (List y) -> Atom (List (x :: y))
  | _ -> failwith "cons"
           
let car (x:sexpr) : sexpr =
  match x with
  | Atom (List (e::x)) -> e
  | _ -> failwith "car"
           
let cdr (x:sexpr) : sexpr =
  match x with
  | Atom (List (e::x)) -> Atom (List x)
  | _ -> failwith "cdr"


let rec eval (env : env) (e : sexpr) : sexpr = 
  (* si e est un atome, alors retourner simplement e *)
  (* sinon, si e est un symbole x, chercher le couple (x,v) dans l'environnement, 
   *                        et retourner simplement la valeur v. 
   *                        PS: on pourra utiliser la fonction List.assoc *)
  (* sinon, si e est une application (Call), alors évaluer l'application (cf. eval_call) *)
  match e with
  | Atom a -> e
  | Symbol s -> List.assoc s env 
  | Special s -> e
  | Call sl -> eval_call env sl
  
and eval_call (env : env) (es : sexpr list) : sexpr = 
  (* `(f a1 a2 ... an)` *)
  (* si l'expression f à appliquer est une forme spéciale (cf. is_special), évaluer la forme speciale (cf. eval_special). *)
  (* sinon, évaluer tout les éléments f, a1, a2, a3 ... de l'application ; on obtient les valeurs vf, va1, va2, ... vn ; 
   * puis appeler la fonction apply. *)
  match es with
  | (Special s)::args -> eval_special env es
  | _ -> apply (List.map (eval env) es)
  
and eval_special (env : env) (es : sexpr list) : sexpr = match es with
  | [Special If;e1;e2;e3] -> 
      (match eval env e1 with
       | (Atom (Bool true)) -> eval env e2
       | _ -> eval env e3
      )
  (* 1) si c'est une alternative (If), évaluer la condition.
   *     - si la condition est (Atom(Bool true)), alors, évaluer la conséquence (l'expression <then>).
   *     - sinon, évaluer l'alternant (l'expression <else>).
   * si c'est une fonction anomyme (lambda),
*)
  | [Special Lambda;Call args;body] -> 
      Atom (Fun (env,(List.map (function Symbol name -> name | _ -> assert false) args,body)))
  | [Special Let;Call[name;e1];e2] -> 
      let es' = Call [Call [Special Lambda;Call [name];e2];e1] in 
      eval env es'
  (* Remarquez que l'expression   (let (x e1) e2)    est réécrit en   ((lambda (x) e2) e1)   *)
  | _ -> failwith "eval_special"
  
and apply (es : sexpr list) : sexpr =
  match es with
  | Atom (Primitive p) :: args -> apply_primitive p args
  | Atom (Fun (env,code)) :: args -> apply_function (env,code) args 
  | _ -> failwith "apply"
   (* `(vf va1 va2 ... vn)`
    * --> si vf est une primitive, appliquer la primitive vf à la liste d'arguments va1, va2, ... vn (cf. apply_primitive)
    * --> si vf est une fonction (Fun), appliquer la fonction vf à la liste d'arguments va1, va2, ... vn (cf. apply_function)
*)

and apply_primitive (p : primitive) (args : sexpr list) : sexpr = 
  (* Convertir en int *)
  let to_int (x: sexpr) =
    match x with
    | Atom (Int n) -> n
    | _ -> failwith "apply_primitive: invalid argument"
  in
  match p,args with
  (* PS: on pourrait aussi faire un (+) n-aire, avec fold_left *)
  | Add,(Atom (Int n)::tl) -> Atom (Int (List.fold_left ( + ) n (List.map to_int tl) ))
  | Sub,(Atom (Int n)::tl) -> Atom (Int (List.fold_left ( - ) n (List.map to_int tl) ))
  | Mul,(Atom (Int n)::tl) -> Atom (Int (List.fold_left ( * ) n (List.map to_int tl) ))
  | Div,(Atom (Int n)::tl) -> Atom (Int (List.fold_left ( / ) n (List.map to_int tl) ))
  | Eq, (n::tl) -> Atom (Bool (List.for_all (fun x -> x=n) tl ))
  | Lt, _ -> 
    let rec aux (l:sexpr list) : bool =
      match l with 
      | [] -> true
      | x::y::l -> 
        (match x,y with 
        | Atom (Int x),Atom (Int y') -> if x >= y' then false else aux (y::l)
        | Atom (Str_ x),Atom (Str_ y') -> if x >= y' then false else aux (y::l)
        | _ -> failwith "apply_primitive: invalid argument"
        )
      | x::l -> true
    in Atom (Bool (aux args))
  | Cons,[x ; y] -> cons x y
  | Car, [x] -> car x
  | Cdr, [x] -> cdr x
  | _ -> failwith "apply_primitive"

and apply_function (vf : env * code) (args : sexpr list) : sexpr =
  (* `(vf va1 va2 ... vn)`
   * Décomposer la valeur fonctionnelle vf : c'est un couple (env',code) où :
   * - env' est l'environnement de la fermeture,
   * - code est le code de la fonction : c'est un couple (xs,e) ou 
   *                                      - xs = x1,x2,...,xm est la liste des arguments formels de vf  
   *                                      - l'expression e est le corps de la fonction
   * 
   * Lancer une exception si m est différent de n (il n'y a pas d'application partielle en Scheme).
   *
   * Enrichir l'environnement env' en liant les argument formels xk aux arguments effectifs vak (cf. extend_env), 
   * appelons `lenv` ce nouvel environnement.
   *
   * Enfin, évaluer le corps `e` de la fonction dans l'environnement `lenv` (cf. eval).
  *)
  let env,(xs,e) = vf in
  if List.length xs != List.length args then failwith "apply_function"
  else eval (extend_env env xs args) e


and extend_env (env : env) (xs : string list) (vs : sexpr list)  : env = 
  (* Posons xs = x1,x2, ...,xn et vs = v1, v2, ..., vn.
   * 
   * Enrichir l'environnement local env, en liant chaque variable xi à la valeur vi : 
   * 1) construire la liste de couple [(x1,v1);(x2,v2); ...;(xn,vn)] 
   *    (PS: on pourra utiliser la fonction List.combine) 
   *    On obtient une liste l.
   * 2) concaténer l à la tête de env. On obtient l'environnement souhaité.
  *)
  (List.combine xs vs) @ env


(*****************************)

(* ne semble pas nécessaire 
and is_special (_es : sexpr list) : bool =
  failwith "Not implemented"
*)


let example_1 : string = "(+ 1 2)"

let sexpr_example_1 : sexpr =
  Call
    [ Atom (Primitive Add)
    ; Atom (Int 1)
    ; Atom (Int 2)
    ]

let example_2 : string = "(let (y (lambda (x) (+ x 10))) (y 2))"

let sexpr_example_2 : sexpr =
  Call
    [ Special Let
    ; Call
      [ Symbol "y"
      ; Call
        [ Special Lambda
        ; Call [ Symbol "x" ]
        ; Call
          [ Atom (Primitive Add)
          ; Symbol "x"
          ; Atom (Int 10)
          ]
        ]
      ]
    ; Call [ Symbol "y"; Atom (Int 2) ]
    ]

let example_3 : string =
  "((lambda (x) (let (a 10) (let (x 20) (+ x 1)))) 20000)"

let sexpr_example_3 : sexpr =
  Call
    [ Call
      [ Special Lambda
      ; Call [ Symbol "x" ]
      ; Call
        [ Special Let
        ; Call [ Symbol "a"; Atom (Int 10) ]
        ; Call
          [ Special Let
          ; Call [ Symbol "x"; Atom (Int 20) ]
          ; Call
            [ Atom (Primitive Add)
            ; Symbol "x"
            ; Atom (Int 1)
            ]
          ]
        ]
      ]
    ]

(* LES TESTS *)

let examples = 
    [ "(+ 5 2)"
    ; "(+ 0 4 1 2)"
    ; "(- 1 2)"
    ; "(- 5 2 1 0 3)"
    ; "(* 0 5)"
    ; "(* 2 3 1 4)"
    ; "(/ 5 2)"
    ; "(/ 1 2)"
    ; "(/ 8 2 1 2)"
    ; "(< 1 2)"
    ; "(< 2 1)"
    ; "(< 2 2)"
    ; "(< 1 2 3 5 9)"
    ; "(< 1 2 3 3 7)"
    ; "(< \"a\" \"ab\" \"c\")"
    ; "(< \"ab\" \"ab\" \"c\")"
    ; "(= 1 2)"
    ; "(= 2 1)"
    ; "(= 2 2)"
    ; "(= 2 2 2 2 2)"
    ; "(= 2 2 3 3 3)"
    ; "(= true true true)"
    ; "(= false false true)"
    ; "(if true 1 2)"
    ; "(if false 1 2)"
    ; "(if (= 1 2) true false)"
    ; "(if (< 1 2) true false)"
    ; "(cons 1 (cons 2 (cons 3 '())))"
    ; "(car (cons 1 (cons 2 (cons 3 '()))))"
    ; "(cdr (cons 1 (cons 2 (cons 3 '()))))"
    ; example_1
    ; example_2
    ; example_3
    ]


let main () =
  let test _ t =
    print_string t;
    print_string "\t  --->\t";
    let prog = Parser.parse t in
    let t = List.map (eval initial_env) prog in
    List.fold_left (fun _ x -> print_endline (Parser.string_of_sexpr x)) () t;
    ()
  in
  List.fold_left test () examples;
  ()

let () = main ()
