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

(* A general type which includes all kind of types *)
Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | code : Result.

Scheme Equality for Result.

(* An environment which maps variable names (strings) to the Result type  *)
Definition Env := string -> Result.
(* Initial environment *)
Definition env : Env := fun x => err_undecl. 

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
  | defaultS : BreakContinue
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

(*
Inductive Vector :=
  | vector_decl : string -> LstElement -> Vector
  | vector_assign : string -> LstElement -> Vector.


Inductive Define :=
  | define_nat : AExp -> string -> Define
  | define_string : string -> string -> Define.
*)

Inductive FuncAExp :=
  | amax: AExp -> AExp -> FuncAExp
  | amin: AExp -> AExp -> FuncAExp
  | apow: AExp -> AExp -> FuncAExp.

Inductive SwitchValue :=
  | nCase : AExp -> SwitchValue
  | sCase : string -> SwitchValue
  | dCase : BreakContinue -> SwitchValue.

Coercion nCase: AExp >-> SwitchValue.
Coercion sCase : string >-> SwitchValue.
Coercion dCase : BreakContinue >-> SwitchValue.

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
  | switchSeq : SwitchValue -> Stmt -> BreakContinue -> Stmt
  | switchNat : AExp -> Stmt -> Stmt
  | switchString : string -> Stmt -> Stmt
  | fordo : Stmt -> BExp -> Stmt -> Stmt -> Stmt
  | define_nat : AExp -> string -> Stmt
  | define_string : string -> string -> Stmt
  | vector_decl : string -> LstElement -> Stmt
  | vector_assign : string -> LstElement -> Stmt
  | break_loop : Stmt.

(*  SEMANTICA   *)

Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Definition max_fun (n1 n2 : AExp) : ErrorNat :=
  match n1, n2 with
    | num a, num b => if Nat.ltb a b
                      then b
                      else a
    | _, _ => error_nat
end.

Definition min_fun (n1 n2 : AExp) : ErrorNat :=
  match n1, n2 with
    | num a, num b => if Nat.ltb a b
                      then a
                      else b
    | _, _ => error_nat
end.

Definition check_eq_over_types (t1 : Result)(t2 : Result) : bool :=
  match t1 with
  | err_undecl => match t2 with
                   | err_undecl => true
                   | _ => false
                   end
  | err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
  | default => match t2 with
                   | default => true
                   | _ => false
                   end
  | code => match t2 with
                   | code => true
                   | _ => false
                   end
  | res_nat ErrorNat => match t2 with
                   | res_nat ErrorNat => true
                   | _ => false
                   end
  | res_bool ErrorBool => match t2 with
                   | res_bool ErrorBool => true
                   | _ => false
                   end
  end.

Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem.

Scheme Equality for Mem.

Definition EnvM := string -> Mem.
Definition MemLayer := Mem -> Result.
Definition Stack := list Env.

Inductive Config :=
  | config : nat -> Env -> MemLayer -> Stack -> Config.

Definition update_env (env: EnvM) (x: string) (n: Mem) : EnvM :=
  fun y =>
      if (andb (string_beq x y ) (Mem_beq (env y) mem_default))
      then
        n
      else
        (env y).

Definition env1 : EnvM := fun x => mem_default.

Definition update_mem (mem : MemLayer) (env : EnvM) (x : string) (type : Mem) (v : Result) : MemLayer :=
  fun y =>
    if (Mem_beq y type)
      then
        if (Mem_beq (env x) mem_default)
        then err_undecl
        else
          if (Mem_beq (env x) y)
          then 
            if (check_eq_over_types (mem y) v)
            then v
            else err_assign
          else mem y
      else mem y.

(*Predefined functions.*)
Notation "'fMaxim' A ~ B" := (max_fun A B) (at level 60).
Notation "'fMinim' A ~ B" := (min_fun A B) (at level 60).
Notation "'fPow' A ~ B" := (apow A B) (at level 60).

(*Break & Continue*)  
Notation "Break!" := (break) (at level 50).
Notation "Default!" := (defaultS) (at level 50).
Notation "Continue!" := (continue) (at level 50).
Notation "'BreakLoop'" := (break_loop) (at level 40).
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
Notation "'fors' ( A ~ B ~ C ) '{' S '}'" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'Ifs' '(' A ')' '{' B '}'" := (ifthen A B) (at level 70).
Notation "'Ifd' '(' A ')' '{' B '}' 'Else' '{' C '}'" := (ifthenelse A B C) (at level 70).
Notation "'While' '(' A ')' '{' B '}'" := (while A B) (at level 90).
(*Switch*)

Notation "'SwitchNat' ( A ) { S }" := (switchNat A S) (at level 80).
Notation "'case:' A --> B C" := (switchSeq A B C)(at level 80).

Notation "'SwitchString' ( A ) { S }" := (switchString A S) (at level 80).

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

(* Notatations used for the Big-Step semantics *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).

(* Big-Step semantics for arithmetic operations *)
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | res_nat x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_ErrorNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_ErrorNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_ErrorNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_ErrorNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_ErrorNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

(*
Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive feval : FuncAExp -> Env -> AExp -> Prop :=
  | f_max : forall a1 a2 i1 i2 sigma,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    if(i1 >' i2) then (amax a1 a2) =[ sigma ]=> i1
    else amax(a1 a2) =[ sigma ]=> i2
  | f_min : forall a1 a2 i1 i2 sigma,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    if(i1 <' i2) then (amin a1 a2) =[ sigma ]=> i1
    else amin(a1 a2) =[ sigma ]=> i2
where "F =[ sigma ] => A" := (feval a sigma n).
*)

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> error_bool
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | res_bool x => x
                                                | _ => error_bool
                                               end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_ErrorBool i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_ErrorBool i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_ErrorBool i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_ErrorBool i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Definition update (env : Env) (x : string) (v : Result) : Env :=
  fun y =>
    if (eqb y x)
    then v
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   (iNat x ::= a) -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (res_nat i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (res_bool i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_forfalse : forall e1 e2 e3 s sigma,
    e2 ={ sigma }=> false ->
    fordo e1 e2 e3 s -{ sigma }-> sigma
| e_fortrue : forall e1 e2 e3 s sigma sigma',
    e2 ={ sigma }=> true ->
    (e1 ;; while e2 (s ;; e3)) -{ sigma }-> sigma' ->
    fordo e1 e2 e3 s -{ sigma }-> sigma'
| e_break_loop : forall stmt sigma,
    stmt -{ sigma }-> match stmt with
                        | while b s => sigma
                        | _ => sigma
                       end
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').


Definition Exemplu1 :=
  15 #defineNat "PunctajMaxim";;
  "PanzariuAdi" #defineString "nume";;

  iNat "age" ::= 21 ;;
  iBool "major" ::= btrue ;;
  iVector "note" ::= (6 .-> 7 .-> 8 .-> 9 .-> 10) ;;
  iVector "prieteni" ::= ("Andrei" .-> "Emi" .-> "Bogdan") ;;
 
  iNat "contor" ::= 0 ;;

  Ifs ( "contor" <' 5) {
    "contor" :n= 6
  }
  ;;
  While( "contor" <' 100) {
    "contor" :n= "contor" +' 1 ;;
    BreakLoop
  } 
  ;;
  SwitchNat (2) { 
        case: 1 -->
          "n1" :n= 1
        Break!
        ;;
        case: 2 -->
          "n1" :n= 2
        Break!
        ;;
        case: Default! -->
          "n1" :n= 3;;
          "n2" :n= 5
        Break!
  }.
  
Example Exemplu2 :
  exists sigma',
  (
    iNat "i" ::= 0;;
    While ("i" <' 20)
    {
      "i" :n= ("i" +' 2);;
      BreakLoop
    }
  )-{ env }-> sigma'   /\ sigma' "i" = res_nat 2.


Proof.
 eexists.
 split.
  - eapply e_seq; eauto.
    + eapply e_nat_decl. eauto.

