// T-501-FMAL, Spring 2022, Assignment 3

(*
STUDENT NAMES HERE: ...


*)

module Assignment3

// (You can ignore this line, it stops F# from printing some messages
// about references in some cases.)
#nowarn "3370";;

////////////////////////////////////////////////////////////////////////
// Problem 1                                                          //
////////////////////////////////////////////////////////////////////////

(* ANSWER 1 HERE:
   (i)
        it is 51 because in the static scope it uses x where the function was first created. So in snd (g 40) it uses let x (f 20)
        which returned 11. so in (g 40) it is 11 + 40 = 51.
  (ii)
        Here the answer is 53 because in the dynamic scope we use the x where it was last called so first the x is 10 and then 11 and then 13
        then we use x = 13 in (g 40) = 53, therefore the answer is 53

*)



////////////////////////////////////////////////////////////////////////
// Problem 2                                                          //
////////////////////////////////////////////////////////////////////////

// fun1: ’a -> (’a -> ’b) -> ’b
let fun1 x k = k x 

// fun2: (’a -> ’b) -> ((’a -> ’c) -> ’d) -> (’b -> ’c) -> ’d
let fun2 f t k = failwith "Not implemented"

// fun3: (’a -> ’b -> ’c) -> ’a * ’b -> ’c
let fun3 f (x, y) = f x y

// fun4: (’a -> ’b -> ’a) -> ’a * ’b -> ’a
let fun4 f (x, y) = f (f x y) (y)

// fun5: (’a -> ’a -> ’a) -> ’a * ’a -> ’a
let fun5 f (x, y) = f (f y x) (f y x) 

////////////////////////////////////////////////////////////////////////
// Problem 3                                                          //
////////////////////////////////////////////////////////////////////////

(* ANSWER 3 HERE:
     (i)

    (ii)

   (iii)

    (iv)

     (v)
*)



////////////////////////////////////////////////////////////////////////
// Some type declarations, do not change these                        //
////////////////////////////////////////////////////////////////////////

type expr =
    | Var of string
    | Let of string * expr * expr
    | Call of expr * expr
    | LetFun of string * string * expr * expr
    | Num of int
    | Plus of expr * expr
    | Minus of expr * expr
    | Times of expr * expr
    | Divide of expr * expr
    | Neg of expr
    | True
    | False
    | Equal of expr * expr
    | Less of expr * expr
    | ITE of expr * expr * expr
    | Pair of expr * expr                       // pairing
    | Fst of expr                               // first component
    | Snd of expr                               // second component
type 'a envir = (string * 'a) list

type typ =
    | TVar of typevar
    | Int
    | Bool
    | Fun of typ * typ
    | Prod of typ * typ                         // product type
and typevar = (tvarkind * int) ref
and tvarkind =
    | NoLink of string
    | LinkTo of typ

type typescheme =
    | TypeScheme of typevar list * typ

type value =
    | I of int
    | B of bool
    | F of string * string * expr * value envir
    | P of expr * expr * value envir            // pair closure

////////////////////////////////////////////////////////////////////////
// Some helper functions, do not change these                         //
////////////////////////////////////////////////////////////////////////

let rec lookup (x : string) (env : 'a envir) : 'a =
    match env with
    | []          -> failwith (x + " not found")
    | (y, v)::env -> if x = y then v else lookup x env

let setTvKind (tv : typevar) (kind : tvarkind) : unit =
    let _, lvl = !tv
    tv := kind, lvl

let setTvLevel (tv : typevar) (lvl : int) : unit =
    let kind, _ = !tv
    tv := kind, lvl

let rec normType (t : typ) : typ =
    match t with
    | TVar tv ->
        match !tv with
        | LinkTo t', _ -> let tn = normType t'
                          setTvKind tv (LinkTo tn); tn
        | _ -> t
    |  _ -> t

let rec union xs ys =
    match xs with
    | []    -> ys
    | x::xs -> if List.contains x ys then union xs ys
               else x :: union xs ys

let rec freeTypeVars (t : typ) : typevar list =
    match normType t with
    | TVar tv      -> [tv]
    | Int          -> []
    | Bool         -> []
    | Fun (t1, t2) -> union (freeTypeVars t1) (freeTypeVars t2)
    | Prod (t1, t2) -> union (freeTypeVars t1) (freeTypeVars t2)

let occursCheck (tv : typevar) (tvs : typevar list) : unit =
    if List.contains tv tvs then failwith "type error: circularity"
    else ()

let pruneLevel (maxLevel : int) (tvs : typevar list) : unit =
    let reducelevel tv =
        let _, lvl = !tv
        setTvLevel tv (min lvl maxLevel)
    List.iter reducelevel tvs

let rec linkVarToType (tv : typevar) (t : typ) : unit =
    let _, lvl = !tv
    let tvs = freeTypeVars t
    occursCheck tv tvs;
    pruneLevel lvl tvs;
    setTvKind tv (LinkTo t)

let paren b s = if b then "(" + s + ")" else s

let prettyprintType (t : typ) : string =
    let rec prettyprintType' t acc =
        match normType t with
        | TVar v ->
            match !v with
            | NoLink name, _ -> name
            | _ -> failwith "we should not have ended up here"
        | Int -> "int"
        | Bool -> "bool"
        | Fun (t1, t2) ->
            let s1 = prettyprintType' t1 true
            let s2 = prettyprintType' t2 false
            paren acc (sprintf "%s -> %s" s1 s2)
        | Prod (t1, t2) ->
            let s1 = prettyprintType' t1 true
            let s2 = prettyprintType' t2 true
            paren acc (sprintf "%s * %s" s1 s2)
    prettyprintType' t false

let tyvarno : int ref = ref 0
let newTypeVar (lvl : int) : typevar =
    let rec mkname i res =
            if i < 26 then char(97+i) :: res
            else mkname (i/26-1) (char(97+i%26) :: res)
    let intToName i = new System.String(Array.ofList('\'' :: mkname i []))
    tyvarno := !tyvarno + 1;
    ref (NoLink (intToName (!tyvarno)), lvl)

let rec generalize (lvl : int) (t : typ) : typescheme =
    let notfreeincontext tv =
        let _, linkLvl = !tv
        linkLvl > lvl
    let tvs = List.filter notfreeincontext (freeTypeVars t)
    TypeScheme (tvs, t)

let rec copyType (subst : (typevar * typ) list) (t : typ) : typ =
    match t with
    | TVar tv ->
        let rec loop subst =
            match subst with
            | (tv', t') :: subst -> if tv = tv' then t' else loop subst
            | [] -> match !tv with
                    | NoLink _, _ -> t
                    | LinkTo t', _ -> copyType subst t'
        loop subst
    | Fun (t1,t2) -> Fun (copyType subst t1, copyType subst t2)
    | Int         -> Int
    | Bool        -> Bool
    | Prod (t1, t2) -> Prod (copyType subst t1, copyType subst t2)

let specialize (lvl : int) (TypeScheme (tvs, t)) : typ =
    let bindfresh tv = (tv, TVar (newTypeVar lvl))
    match tvs with
    | [] -> t
    | _  -> let subst = List.map bindfresh tvs
            copyType subst t



////////////////////////////////////////////////////////////////////////
// Problem 4                                                          //
////////////////////////////////////////////////////////////////////////

let rec unify (t1 : typ) (t2 : typ) : unit =
    let t1' = normType t1
    let t2' = normType t2
    match t1', t2' with
    | Int,  Int  -> ()
    | Bool, Bool -> ()
    | Fun (t11, t12), Fun (t21, t22) -> unify t11 t21; unify t12 t22
    | TVar tv1, TVar tv2 ->
        let _, tv1level = !tv1
        let _, tv2level = !tv2
        if tv1 = tv2                then ()
        else if tv1level < tv2level then linkVarToType tv1 t2'
                                    else linkVarToType tv2 t1'
    | TVar tv1, _ -> linkVarToType tv1 t2'
    | _, TVar tv2 -> linkVarToType tv2 t1'
    | _, _ -> failwith ("cannot unify " + prettyprintType t1' + " and " + prettyprintType t2')



////////////////////////////////////////////////////////////////////////
// Problem 5                                                          //
////////////////////////////////////////////////////////////////////////

let rec infer (e : expr) (lvl : int) (env : typescheme envir) : typ =
    match e with
    | Var x  -> specialize lvl (lookup x env)
    | Let (x, erhs, ebody) ->
        let lvl' = lvl + 1
        let tx = infer erhs lvl' env
        let env' = (x, generalize lvl tx) :: env
        infer ebody lvl env'
    | Call (efun, earg) ->
        let tf = infer efun lvl env
        let tx = infer earg lvl env
        let tr = TVar (newTypeVar lvl)
        unify tf (Fun (tx, tr)); tr
    | LetFun (f, x, erhs, ebody) ->
        let lvl' = lvl + 1
        let tf = TVar (newTypeVar lvl')
        let tx = TVar (newTypeVar lvl')
        let env' = (x, TypeScheme ([], tx))
                      :: (f, TypeScheme ([], tf)) :: env
        let tr = infer erhs lvl' env'
        let () = unify tf (Fun (tx, tr))
        let env'' = (f, generalize lvl tf) :: env
        infer ebody lvl env''
    | Num i -> Int
    | Plus (e1, e2) ->
        let t1 = infer e1 lvl env
        let t2 = infer e2 lvl env
        unify Int t1; unify Int t2; Int
    | Minus (e1, e2) ->
        let t1 = infer e1 lvl env
        let t2 = infer e2 lvl env
        unify Int t1; unify Int t2; Int
    | Times (e1, e2) ->
        let t1 = infer e1 lvl env
        let t2 = infer e2 lvl env
        unify Int t1; unify Int t2; Int
    | Divide (e1, e2) ->
        let t1 = infer e1 lvl env
        let t2 = infer e2 lvl env
        unify Int t1; unify Int t2; Int
    | Neg e ->
        let t = infer e lvl env
        unify Int t; Int
    | True  -> Bool
    | False -> Bool
    | Equal (e1, e2) ->
        let t1 = infer e1 lvl env
        let t2 = infer e2 lvl env
        unify t1 Int; unify t2 Int;
        Bool
    | Less (e1, e2) ->
        let t1 = infer e1 lvl env
        let t2 = infer e2 lvl env
        unify Int t1; unify Int t2; Bool
    | ITE (e, e1, e2) ->
        let t1 = infer e1 lvl env
        let t2 = infer e2 lvl env
        unify Bool (infer e lvl env); unify t1 t2; t1

    | Pair (e1, e2) -> failwith "Not implemented"
    | Fst e -> failwith "Not implemented"
    | Snd e -> failwith "Not implemented"

let inferTop e =
    tyvarno := 0; prettyprintType (infer e 0 [])



////////////////////////////////////////////////////////////////////////
// Problem 6                                                          //
////////////////////////////////////////////////////////////////////////

let rec eval (e : expr) (env : value envir) : value =
    match e with
    | Var x  ->  lookup x env
    | Let (x, erhs, ebody) ->
         let v = eval erhs env
         let env' = (x, v) :: env
         eval ebody env'
    | Call (efun, earg) ->
         let clo = eval efun env
         match clo with
         | F (f, x, ebody, env0) ->
             let v = eval earg env
             let env' = (x, v) :: (f, clo) :: env0
             eval ebody env'
         | _   -> failwith "expression called not a function"
    | LetFun (f, x, erhs, ebody) ->
         let env' = (f, F (f, x, erhs, env)) :: env
         eval ebody env'
    | Num i -> I i
    | Plus  (e1, e2) ->
         match eval e1 env, eval e2 env with
         | I i1, I i2 -> I (i1 + i2)
         | _ -> failwith "argument of + not integers"
    | Minus  (e1, e2) ->
         match eval e1 env, eval e2 env with
         | I i1, I i2 -> I (i1 - i2)
         | _ -> failwith "arguments of - not integers"
    | Times (e1, e2) ->
         match eval e1 env, eval e2 env with
         | I i1, I i2 -> I (i1 * i2)
         | _ -> failwith "arguments of * not integers"
    | Divide (e1, e2) ->
         match eval e1 env, eval e2 env with
         | I i1, I i2 ->
             if i2 = 0 then failwith "division by 0"
             else I (i1 / i2)
         | _ -> failwith "arguments of / not integers"
    | Neg e ->
         match eval e env with
         | I i -> I (- i)
         | _ -> failwith "argument of negation not an integer"
    | True  -> B true
    | False -> B false
    | Equal (e1, e2) ->
         match eval e1 env, eval e2 env with
         | I i1, I i2 -> B (i1 = i2)
         | _ -> failwith "arguments of = not integers"
    | Less (e1, e2) ->
         match eval e1 env, eval e2 env with
         | I i1, I i2 -> B (i1 < i2)
         | _ -> failwith "arguments of < not integers"
    | ITE (e, e1, e2) ->
         match eval e env with
         | B b -> if b then eval e1 env else eval e2 env
         | _ -> failwith "guard of if-then-else not a boolean"

    | Pair (e1, e2) -> failwith "Not implemented"
    | Fst e -> failwith "Not implemented"
    | Snd e -> failwith "Not implemented"



////////////////////////////////////////////////////////////////////////
// Problem 7                                                          //
////////////////////////////////////////////////////////////////////////

(* ANSWER 7 HERE:

*)



