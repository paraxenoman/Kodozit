(* Kodozit.Seos Formal Theory @ Paraxenoman *)

Require Import Kodozit.Utils.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import ExtLib.Structures.Monad.
Import ListNotations.
Import MonadNotation.
Open Scope list_scope.
Open Scope string_scope.
Open Scope bool_scope.
Open Scope monad_scope.

Definition TypeName : Type := string.
Definition VarName : Type := string.
Definition elem : Type := string.

Inductive prim : Type :=
  | Prm_Left : prim
  | Prm_Right : prim.

Definition prim_beq (p1 p2 : prim) : bool :=
  match p1, p2 with
  | Prm_Left, Prm_Left => true
  | Prm_Right, Prm_Right => true
  | _, _ => false
  end.

Inductive core_term : Type :=
  | CT_Sort : nat -> core_term
  | CT_Unit : core_term
  | CT_Elem : elem -> core_term
  | CT_Prim : prim -> core_term
  | CT_Sing : core_term -> core_term
  | CT_Nat : core_term
  | CE_Unit : core_term
  | CE_Elem : elem -> core_term
  | CE_Prim : prim -> core_term
  | CE_Sing : core_term -> core_term
  | CE_Nat : nat -> core_term
  | CE_App : core_term -> core_term -> core_term.

Inductive value : Type :=
  | NT_Sort : nat -> value
  | NT_Unit : value
  | NT_Elem : elem -> value
  | NT_Prim : prim -> value
  | NT_Sing : value -> value
  | NT_Nat : value
  | NE_Unit : value
  | NE_Elem : elem -> value
  | NE_Prim : prim -> value
  | NE_Sing : value -> value
  | NE_Nat : nat -> value.

(* Independent *)

Inductive error : Type :=
  | Err_NotImplemented : error
  | Err_InvalidApp : core_term -> core_term -> error
  | TypeErr_Mismatch : core_term -> core_term -> error
  | TypeErr_ListMismatch : list core_term -> list core_term -> error.

Inductive result (A : Type) : Type :=
  | Ok : A -> result A
  | Err : error -> result A.

Arguments Ok {A} _.
Arguments Err {A} _.

#[global]
Instance Monad_result : Monad result :=
{ ret :=
    fun {A : Type} (x : A) =>
      Ok x;

  bind :=
    fun {A B : Type}
        (r : result A)
        (f : A -> result B) =>
      match r with
      | Ok x  => f x
      | Err e => Err e
      end
}.

Fixpoint map_result 
    {I R: Type}
    (f : I -> result R)
    (Ts : list I)
    : result (list R) :=
  match Ts with
  | [] => Ok []
  | T1 :: rest =>
      T1' <- f T1 ;;
      rest' <- map_result f rest ;;
      Ok (T1' :: rest')
  end.

Fixpoint validate_list
      {A : Type}
      (f : A -> result unit)
      (Ts : list A)
    : result unit :=
    match Ts with
    | [] => Ok tt
    | T1 :: rest =>
        _ <- f T1 ;;
        validate_list f rest
    end.

Inductive TypeBinding : Type :=
  | BindCombType : TypeName -> core_term -> list string -> list core_term -> TypeBinding
  | CloseCombType : TypeName -> TypeBinding.

Definition type_context : Type := list TypeBinding.

Record machine_state : Type := {
  ms_type_ctx : type_context;
  ms_last_type : value;
  ms_last_value : value
}.

Definition initial_state : machine_state :=
  {| ms_type_ctx := [];
     ms_last_type := NT_Unit;
     ms_last_value := NE_Unit |}.

Fixpoint value_beq (v1 v2 : value) : bool :=
  match v1, v2 with
  | NT_Sort n1, NT_Sort n2 => Nat.eqb n1 n2
  | NT_Unit, NT_Unit => true
  | NT_Elem e1, NT_Elem e2 => String.eqb e1 e2
  | NT_Prim p1, NT_Prim p2 => prim_beq p1 p2
  | NT_Sing iv1, NT_Sing iv2 => value_beq iv1 iv2
  | NT_Nat, NT_Nat => true
  | NE_Unit, NE_Unit => true
  | NE_Elem e1, NE_Elem e2 => String.eqb e1 e2
  | NE_Prim p1, NE_Prim p2 => prim_beq p1 p2
  | NE_Sing iv1, NE_Sing iv2 => value_beq iv1 iv2
  | NE_Nat n1, NE_Nat n2 => Nat.eqb n1 n2
  | _, _ => false
  end.

Fixpoint eval_list (f : core_term -> result value) (ts : list core_term)
  : result (list value) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      v <- f t ;;
      vs <- eval_list f rest ;;
      Ok (v :: vs)
  end.

Fixpoint infer_list
    {A : Type}
    (f : type_context -> A -> result value)
    (Gamma : type_context)
    (ts : list A)
    {struct ts}
  : result (list value) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      T <- f Gamma t ;;
      Ts <- infer_list f Gamma rest ;;
      Ok (T :: Ts)
  end.

Definition eval_app (a b : value) : result value :=
  match b, b with
  | _, _ => Err (Err_NotImplemented)
  end.

Fixpoint eval (tm : core_term) : result value :=
  match tm with
  | CT_Sort u => Ok (NT_Sort u)
  | CT_Unit => Ok NT_Unit
  | CT_Elem e => Ok (NT_Elem e)
  | CT_Prim p => Ok (NT_Prim p)
  | CT_Sing e => 
    v <- eval e;;
    Ok (NT_Sing v)
  | CT_Nat => Ok NT_Nat
  | CE_Unit => Ok NE_Unit
  | CE_Elem e => Ok (NE_Elem e)
  | CE_Prim p => Ok (NE_Prim p)
  | CE_Sing e => 
    v <- eval e;;
    Ok (NE_Sing v)
  | CE_Nat n => Ok (NE_Nat n)
  | CE_App a b => 
      va <- eval a;;
      vb <- eval b;;
      eval_app va vb
  end.

Fixpoint infer
    (Gamma : type_context)
    (tm : core_term)
    {struct tm}
  : result value :=
  match tm with
  | CT_Sort u => Ok (NT_Sort (S u))
  | CT_Unit => Ok (NT_Sort 0)
  | CT_Elem _ => Ok (NT_Sort 0)
  | CT_Prim _ => Ok (NT_Sort 0)
  | CT_Sing _ => Ok (NT_Sort 0)
  | CT_Nat => Ok (NT_Sort 0)
  | CE_Unit => Ok NT_Unit
  | CE_Elem e => Ok (NT_Elem e)
  | CE_Prim p => Ok (NT_Prim p)
  | CE_Sing e => 
    _ <- infer Gamma e;;
    v <- eval e;;
    Ok (NT_Sing v)
  | CE_Nat _ => Ok NT_Nat
  | CE_App a b => 
      ta <- infer Gamma a;;
      tb <- infer Gamma b;;
      match ta, tb with
      | _, _ => Err (Err_NotImplemented)
      end
  end.

Definition eval_typed
    (Gamma : type_context)
    (tm : core_term)
  : result (value * value) :=
    T <- infer Gamma tm ;;
    v <- eval tm ;;
    Ok (T, v).
