Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.
Open Scope list_scope.

(* ErrorNat encapsulates the constructor error_nat 
   which is useful in the case of arithmetic operations like division by 0*)

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.

(* Section for AExp *)
Inductive AExp :=
  | avar: string -> AExp (* Var ~> string *)
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp.

Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp. (* Var ~> string *)

(* Section for BExp *)
Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.

(* Section for Statements *)
Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt
  | bool_decl: string -> BExp -> Stmt
  | nat_assign : string -> AExp -> Stmt
  | bool_assign : string -> BExp -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | switch : AExp -> Stmt.

Notation "A => switch" := (switch A) (at level 31, right associativity).
Check 2 => switch.

Inductive Vector :=
  | vector_decl : string -> Stmt -> Vector
  | vector_assign : string -> Stmt -> Vector.

Inductive Define :=
  | define_nat : AExp -> string -> Define
  | define_string : string -> string -> Define.

Notation "A #defineNat B" := (define_nat A B) (at level 50). 
Notation "A #defineString B" := (define_string A B) (at level 50).

Check 15 #defineNat "maxPoints".
Check "a" #defineString "b".

Inductive FuncAExp :=
  | amax: AExp -> AExp -> FuncAExp
  | amin: AExp -> AExp -> FuncAExp
  | apow: AExp -> AExp -> FuncAExp.

Notation "A maxim? B" := (amax A B) (at level 60).
Notation "A minim? B" := (amin A B) (at level 60).
Notation "A puterea? B" := (apow A B) (at level 60).

Check 1 maxim? 2.
Check 1 minim? 2.
Check 2 puterea? 3.

Inductive BreakContinue :=
  | break : BreakContinue
  | continue : BreakContinue.

Notation "Break!" := (break) (at level 50).
Notation "Continue!" := (continue) (at level 50).

Check Break!.
