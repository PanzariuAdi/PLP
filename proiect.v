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

Inductive BreakContinue :=
  | break : BreakContinue
  | continue : BreakContinue.

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
  | switchNatSeq : AExp -> Stmt -> BreakContinue -> Stmt
  | switchNat : AExp -> Stmt -> Stmt
  | switchStringSeq : string -> Stmt -> BreakContinue -> Stmt
  | switchString : string -> Stmt -> Stmt.

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

(*Notation for *)
Notation "'fors' ( A ~ B ~ C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).

(*Switch*)

Notation "'SwitchNat' ( A ) { S }" := (switchNat A S) (at level 80).
Notation "'ncase:' A --> B C" := (switchNatSeq A B C)(at level 80).

Notation "'SwitchString' ( A ) { S }" := (switchString A S) (at level 80).
Notation "'scase:' A B C" := (switchStringSeq A B C)(at level 80).

(* Notations used for arithmetic operations *)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity)  .

(* Notations used for boolean operations *)
Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Check iVector "fullName" ::= ("Panzariu" .-> "Ionut" .-> "Adrian").
Check iVector "numbers" ::= (1 .-> 2 .-> 3 .-> 4 .-> 5).
Check iNat "a" ::= 5.

Check (SwitchNat (2) { 
        ncase: 1 -->
          "n1" :n= 1
        Break!
        ;;
        ncase: 2 -->
          "n1" :n= 2;;
          "n2" :n= 3
        Break!
}).

Check "b" :b= btrue.
Check "numbers" :v= ("10" .-> "9" .-> "8").
Check fMaxim 1 ~ 2.
Check fMinim 1 ~ 2.
Check fPow 1 ~ 2.
Check 15 #defineNat "maxPoints".
Check "a" #defineString "b".
Check Break!.
Check Continue!.
