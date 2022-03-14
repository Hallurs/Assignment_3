// T-501-FMAL, Spring 2021, Assignment 3

module Assignment3Tests

open Assignment3


////////////////////////////////////////////////////////////////////////
// Tests for Problem 4                                                //
////////////////////////////////////////////////////////////////////////

// For tests that raise an exception, the exact error message does not
// matter. For tests that have type variables in their output, it does
// not matter what these variables are called (as long as the types are
// equivalent to the types below).

// Define these before trying the tests. You will need to redefine them
// each time you change unify.
let a = ref (NoLink "'a", 0)
let b = ref (NoLink "'b", 0)
let c = ref (NoLink "'c", 0)
let unifyTest t1 t2 =
  a := (NoLink "'a", 0);
  b := (NoLink "'b", 0);
  c := (NoLink "'c", 0);
  unify t1 t2;
  prettyprintType t1

// > unifyTest (Prod (Int, Int)) (Prod (Int, Int));;
// val it: string = "int * int"
// > unifyTest (Prod (Int, Int)) (Prod (Int, Bool));;
// System.Exception: cannot unify int and bool
// > unifyTest (Prod (Bool, Int)) (Prod (Int, Bool));;
// System.Exception: cannot unify bool and int
// > unifyTest (Prod (Int, Int)) (Prod (Int, Prod (Bool, Int)));;
// System.Exception: cannot unify int and bool * int
// > unifyTest (Prod (Prod (Int, Int), Int)) (Prod (Int, Prod (Int, Int)));;
// System.Exception: cannot unify int * int and int
// > unifyTest (TVar a) (Prod (TVar b, TVar c));;
// val it: string = "'b * 'c"
// > unifyTest (TVar a) (Prod (TVar b, TVar a));;
// System.Exception: type error: circularity
// > unifyTest (Prod (TVar a, Bool)) (Prod (Fun (Int, TVar b), TVar c));;
// val it: string = "(int -> 'c) * bool"
// > unifyTest (Prod (TVar a, Bool)) (Prod (Fun (Int, TVar b), TVar a));;
// System.Exception: cannot unify bool and int -> 'c
// > unifyTest (Fun (Prod (TVar a, TVar b), TVar c)) (Fun (TVar c, Prod (Bool, Int)));;
// val it: string = "(bool * int) -> bool * int"
// > unifyTest (Fun (Prod (TVar a, TVar b), TVar a)) (Fun (TVar c, Prod (Bool, Int)));;
// val it: string = "((bool * int) * 'b) -> bool * int"



////////////////////////////////////////////////////////////////////////
// Tests for Problem 5                                                //
////////////////////////////////////////////////////////////////////////

// For tests that raise an exception, the exact error message does not
// matter. For tests that have type variables in their output, it does
// not matter what these variables are called (as long as the types are
// equivalent to the types below).

// > inferTop (Pair (Num 0, True));;
// val it: string = "int * bool"
// > inferTop (Pair (Num 0, Pair (True, Num 1)));;
// val it: string = "int * (bool * int)"
// > inferTop (Fst (Pair (Num 0, Pair (True, Num 1))));;
// val it: string = "int"
// > inferTop (Snd (Pair (Num 0, Pair (True, Num 1))));;
// val it: string = "bool * int"
// > inferTop (Fst (Snd (Pair (Num 0, Pair (True, Num 1)))));;
// val it: string = "bool"
// > inferTop (Snd (Snd (Pair (Num 0, Pair (True, Num 1)))));;
// val it: string = "int"
// > inferTop (Fst (Num 0));;
// System.Exception: cannot unify 'b * 'c and int
// > inferTop (Fst (Fst (Pair (Num 0, Pair (Num 1, Num 2)))));;
// System.Exception: cannot unify 'd * 'e and int
// > inferTop (LetFun ("f", "p", Pair (Snd (Var "p"), Fst (Var "p")), Var "f"));;
// val it: string = "('f * 'g) -> 'g * 'f"
// > inferTop (LetFun ("f", "p", Pair (Snd (Var "p"), Fst (Fst (Var "p"))), Var "f"));;
// val it: string = "(('h * 'i) * 'g) -> 'g * 'h"
// > inferTop (LetFun ("f", "p", Pair (Snd (Var "p"), Fst (Var "p")), Call (Var "f", Pair (Num 0, Num 1))));;
// val it: string = "int * int"
// > inferTop (LetFun ("f", "p", Pair (Snd (Var "p"), Fst (Var "p")), Call (Var "f", Num 0)));;
// System.Exception: cannot unify 'f * 'g and int



////////////////////////////////////////////////////////////////////////
// Tests for Problem 6                                                //
////////////////////////////////////////////////////////////////////////

// For tests that raise an exception, the exact error message does not
// matter.

// > eval (Pair (Divide (Num 1, Num 0), Divide (Num 1, Num 0))) [];;
// val it: value = P (Divide (Num 1, Num 0), Divide (Num 1, Num 0), [])
// > eval (Snd (Pair (Divide (Num 1, Num 0), Num 2))) [];;
// val it: value = I 2
// > eval (Fst (Pair (Divide (Num 1, Num 0), Num 2))) [];;
// System.Exception: division by 0
// > eval (Fst (Var "p")) ["p", P (Divide (Num 1, Num 0), Num 2, [])];;
// System.Exception: division by 0
// > eval (Snd (Var "p")) ["p", P (Divide (Num 1, Num 0), Num 2, [])];;
// val it: value = I 2
// > eval (Let ("x", Num 1, Let ("p", Pair (Var "x", Num 2), Let ("x", Num 3, Fst (Var "p"))))) [];;
// val it: value = I 1
// > eval (Fst (Pair (Var "x", Var "y"))) ["x", I 1; "y", I 2];;
// val it: value = I 1
// > eval (Fst (Pair (Var "x", Var "y"))) ["x", I 1];;
// val it: value = I 1
// > eval (LetFun ("f", "p", Pair (Snd (Var "p"), Fst (Var "p")), Fst (Call (Var "f", Pair (Num 1, Divide (Num 2, Num 0)))))) [];;
// System.Exception: division by 0
// > eval (LetFun ("f", "p", Pair (Snd (Var "p"), Fst (Var "p")), Snd (Call (Var "f", Pair (Num 1, Divide (Num 2, Num 0)))))) [];;
// val it: value = I 1


