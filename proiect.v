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

Inductive LstElement :=
  | natElem: AExp -> LstElement
  | stringElem: string -> LstElement
  | boolElem: BExp -> LstElement
  | lstSequence : LstElement -> LstElement -> LstElement.

Coercion natElem: AExp >-> LstElement.
Coercion stringElem : string >-> LstElement.
Coercion boolElem : BExp >-> LstElement.

Inductive Vector :=
  | vector_decl : string -> LstElement -> Vector
  | vector_assign : string -> LstElement -> Vector.

Inductive Define :=
  | define_nat : AExp -> string -> Define
  | define_string : string -> string -> Define.


Inductive FuncAExp :=
  | amax: AExp -> AExp -> FuncAExp
  | amin: AExp -> AExp -> FuncAExp
  | apow: AExp -> AExp -> FuncAExp.

Inductive BreakContinue :=
  | break : BreakContinue
  | continue : BreakContinue.

(*Predefined functions.*)
Notation "'fMaxim' A ~ B" := (amax A B) (at level 60).
Notation "'fMinim' A ~ B" := (amin A B) (at level 60).
Notation "'fPow' A ~ B" := (apow A B) (at level 60).

(*Break & Continue*)
Notation "Break!" := (break) (at level 50).
Notation "Continue!" := (continue) (at level 50).

(*Define*)
Notation "A #defineNat B" := (define_nat A B) (at level 50). 
Notation "A #defineString B" := (define_string A B) (at level 50).

(*Switch*)
Notation "'fSwitch' A" := (switch A) (at level 30, right associativity).

(*Declarations*)
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'iVector' X ::= A " := (vector_decl X A)(at level 90).

(*Assigns*)
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :v= A" := (vector_assign X A)(at level 90).

Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "S1 .-> S2" := (lstSequence S1 S2) (at level 93, right associativity).

Check iVector "fullName" ::= ("Panzariu" .-> "Ionut" .-> "Adrian").
Check iVector "numbers" ::= (1 .-> 2 .-> 3).
Check fMaxim 1 ~ 2.
Check fMinim 1 ~ 2.
Check fPow 1 ~ 2.
Check fSwitch 2.
Check 15 #defineNat "maxPoints".
Check "a" #defineString "b".
Check Break!.
Check Continue!.