Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.
Open Scope list_scope.

(* ErrorNat encapsulates the constructor error_nat 
   which is useful in the case of arithmetic operations like division by 0*)

Inductive State :=
| pair : nat -> nat -> State.

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
  
Inductive Vector :=
  | vector_decl : string -> Stmt -> Vector
  | vector_assign : string -> Stmt -> Vector.

Inductive Define :=
  | define_nat : AExp -> string -> Define
  | define_bool : BExp -> string -> Define
  | define_string : string -> string -> Define.
  
Inductive FuncAExp :=
  | amax: State -> FuncAExp
  | amin: State -> FuncAExp
  | apow: State -> FuncAExp.
  
Inductive BreakContinue :=
  | break : BreakContinue
  | continue : BreakContinue.