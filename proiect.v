Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

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
  | amod: AExp -> AExp -> AExp
  | amax: AExp -> AExp -> AExp
  | amin: AExp -> AExp -> AExp
  | apow: AExp -> AExp -> AExp.

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
  | nat_decl: string -> AExp -> Stmt (* Declaration Stmt for variables of type nat *)
  | bool_decl: string -> BExp -> Stmt (* Declaration Stmt for variables of type bool *)
  | vector_decl : string -> AExp -> Stmt (* Declaration Stmt for variables of type vector *)
  | nat_assign : string -> AExp -> Stmt (* Assignment Stmt for variables of type nat *)
  | bool_assign : string -> BExp -> Stmt (* Assignment Stmt for variables of type bool *)
  | vector_assign : string -> Stmt -> Stmt. (* Assign Stmt for variables of type vector*)
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | switch : AExp -> Stmt.
  
