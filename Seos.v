(* Kodozit.Seos Formal Theory @ Paraxenoman *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import ExtLib.Structures.Monad.
Import ListNotations.
Import MonadNotation.
Open Scope list_scope.
Open Scope string_scope.
Open Scope bool_scope.
Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

Fixpoint list_eqb {A : Type} (feq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => feq x1 x2 && list_eqb feq t1 t2
  | _, _ => false
  end.

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

Definition pair_eqb
    {A B : Type}
    (eqA : A -> A -> bool)
    (eqB : B -> B -> bool)
    (p1 p2 : A * B)
  : bool :=
  match p1, p2 with
  | (a1, b1), (a2, b2) => eqA a1 a2 && eqB b1 b2
  end.

Inductive type : Type :=
  | T_Hole : string -> type
  | T_Abbr : TypeName -> type
  | T_Elem : elem -> type
  | T_Prim : prim -> type
  | T_TRep : type -> type
  | T_Prod : list type -> type
  | T_Comb : TypeName -> list type -> type
  | T_Map : list (type * type) -> type.

Inductive expr : Type :=
  | E_Var : VarName -> expr
  | E_Elem : elem -> expr
  | E_Prim : prim -> expr
  | E_TRep : type -> expr
  | E_Prod : list expr -> expr
  | E_Comb : expr -> list expr -> expr
  | E_Map : list (expr * expr) -> expr
  | E_App : expr -> expr -> expr.

Inductive value : Type :=
  | V_Elem : elem -> value
  | V_Prim : prim -> value
  | V_TRep : type -> value
  | V_Prod : list value -> value
  | V_Comb : value -> list value -> value
  | V_Map : list (value * value) -> value.

Inductive command : Type :=
  | C_DeclVar : VarName -> expr -> command
  | C_NewTypeAbbr : TypeName -> type -> command
  | C_DeclCombVariant : TypeName -> type -> list string -> list type -> command
  | C_CloseCombType : TypeName -> command
  | C_Eval : expr -> command.

Inductive error : Type :=
  | Err_NotImplemented : error
  (* Ошибки в именах *)
  | Err_UnboundVar : VarName -> error
  | Err_UnboundTypeAbbr : TypeName -> error
  | Err_UnboundHole : string -> error
  | Err_DuplicateVar : VarName -> error
  | Err_UnexpandedVar : VarName -> error
  (* Ошибки в типах *)
  | TypeErr_UseHole : type -> error
  | TypeErr_DeclaredHoleNotUsed : string -> error
  | TypeErr_UndeclaredHole : string -> error
  | TypeErr_DuplicateHoleName : string -> error
  | TypeErr_InvalidApp : type -> type -> error
  | TypeErr_DuplicateType : TypeName -> error
  | TypeErr_DuplicateCombSignature : TypeName -> type -> error
  | TypeErr_DuplicateMapKey : type -> error
  | TypeErr_DuplicateMapPatternKey : type -> error
  | TypeErr_HoleInMapPatternKey : type -> error
  | TypeErr_UnknownCombSignature : error
  | TypeErr_InvalidType : error
  | TypeErr_InvalidProd : type -> error
  | TypeErr_Mismatch : type -> type -> error
  | TypeErr_CombClosed : TypeName -> error
  | TypeErr_CloseUnknownComb : TypeName -> error
  | TypeErr_CombAlreadyClosed : TypeName -> error
  | TypeErr_ListMismatch : list type -> list type -> error
  | TypeErr_UsePrimInDeclComb : type -> error
  (* Ошибки в выражениях *)
  | ExprErr_DuplicateMapKey : expr -> error
  | ExprErr_InvalidProd : expr -> error
  | ExprErr_UseHole : expr -> error
  | ExprErr_InvalidApp : expr -> expr -> error.

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

Notation V_Unit := (V_Prod []).
Notation E_Unit := (E_Prod []).
Notation T_Unit := (T_Prod []).

Inductive TypeBinding : Type :=
  | BindTypeAbbr : TypeName -> type -> TypeBinding
  | BindCombType : TypeName -> type -> list string -> list type -> TypeBinding
  | CloseCombType : TypeName -> TypeBinding.

Definition type_context : Type := list TypeBinding.

Fixpoint type_abbr_lookup (Gamma : type_context) (X : TypeName) : option type :=
  match Gamma with
  | [] => None
  | BindTypeAbbr Y T :: rest =>
      if eqb X Y then Some T else type_abbr_lookup rest X
  | _ :: rest => type_abbr_lookup rest X
  end.

Fixpoint eval_expr_list (f : expr -> result value) (ts : list expr) : result (list value) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      match f t with
      | Err e => Err e
      | Ok v =>
          match eval_expr_list f rest with
          | Err e => Err e
          | Ok vs => Ok (v :: vs)
          end
      end
  end.

Fixpoint contains_prim (T : type) : bool :=
  match T with
  | T_Prim _ => true
  | T_TRep T1 => contains_prim T1
  | T_Prod Ts => existsb contains_prim Ts
  | T_Comb _ Ts => existsb contains_prim Ts
  | T_Map entries =>
      existsb
        (fun entry =>
           let '(K, V) := entry in
           contains_prim K || contains_prim V)
        entries
  | _ => false
  end.

Fixpoint contains_hole (T : type) : bool :=
  match T with
  | T_Hole _ => true
  | T_TRep T1 => contains_hole T1
  | T_Prod Ts => existsb contains_hole Ts
  | T_Comb _ Ts => existsb contains_hole Ts
  | T_Map entries =>
      existsb
        (fun entry =>
           let '(K, V) := entry in
           contains_hole K || contains_hole V)
        entries
  | _ => false
  end.

Fixpoint type_size (T : type) : nat :=
  match T with
  | T_Hole _ => 1
  | T_Abbr _ => 1
  | T_Elem _ => 1
  | T_Prim _ => 1
  | T_TRep T1 => S (type_size T1)
  | T_Prod Ts =>
      S (fold_right (fun T1 n => type_size T1 + n) 0 Ts)
  | T_Comb _ Ts =>
      S (fold_right (fun T1 n => type_size T1 + n) 0 Ts)
  | T_Map entries =>
      S
        (fold_right
           (fun entry n =>
              let '(K, V) := entry in
              type_size K + type_size V + n)
           0
           entries)
  end.

Fixpoint type_context_size (Gamma : type_context) : nat :=
  match Gamma with
  | [] => 0
  | BindTypeAbbr _ T :: rest =>
      type_size T + type_context_size rest
  | BindCombType _ ctor _ args :: rest =>
      type_size ctor
      + fold_right (fun T n => type_size T + n) 0 args
      + type_context_size rest
  | CloseCombType _ :: rest => type_context_size rest
  end.

Record machine_state : Type := {
  ms_type_ctx : type_context;
  ms_last_type : type;
  ms_last_value : value
}.

Definition initial_state : machine_state :=
  {| ms_type_ctx := [];
     ms_last_type := T_Unit;
     ms_last_value := V_Unit |}.

Fixpoint remove_first_eqb
    {A : Type}
    (feq : A -> A -> bool)
    (x : A)
    (xs : list A)
  : option (list A) :=
  match xs with
  | [] => None
  | y :: ys =>
      if feq x y then
        Some ys
      else
        match remove_first_eqb feq x ys with
        | None => None
        | Some ys' => Some (y :: ys')
        end
  end.

Fixpoint permutation_eqb
    {A : Type}
    (feq : A -> A -> bool)
    (xs ys : list A)
  : bool :=
  match xs with
  | [] =>
      match ys with
      | [] => true
      | _ => false
      end
  | x :: xs' =>
      match remove_first_eqb feq x ys with
      | None => false
      | Some ys' => permutation_eqb feq xs' ys'
      end
  end.


Fixpoint type_beq (T1 T2 : type) : bool :=
  match T1, T2 with
  | T_Hole X, T_Hole Y => eqb X Y
  | T_Abbr X, T_Abbr Y => eqb X Y
  | T_Elem e1, T_Elem e2 => eqb e1 e2
  | T_Prim p1, T_Prim p2 => prim_beq p1 p2
  | T_TRep T1', T_TRep T2' => type_beq T1' T2'
  | T_Prod Ts1, T_Prod Ts2 => list_eqb type_beq Ts1 Ts2
  | T_Comb X Ts1, T_Comb Y Ts2 =>
      eqb X Y && list_eqb type_beq Ts1 Ts2
  | T_Map lst1, T_Map lst2 =>
    permutation_eqb (pair_eqb type_beq type_beq) lst1 lst2
  | _, _ => false
  end.

Definition type_mem
    (T : type)
    (Ts : list type)
  : bool :=
  existsb (type_beq T) Ts.

Fixpoint map_pattern_keys_unique
    (seen_keys : list type)
    (entries : list (type * type))
  : bool :=
  match entries with
  | [] =>
      true
  | (key, _) :: rest =>
      if type_mem key seen_keys then
        false
      else
        map_pattern_keys_unique
          (key :: seen_keys)
          rest
  end.

Fixpoint validate_map_pattern_keys
    (T : type)
  : result unit :=
  let fix validate_types
      (Ts : list type)
      : result unit :=
      match Ts with
      | [] => Ok tt
      | T1 :: rest =>
          match validate_map_pattern_keys T1 with
          | Err e => Err e
          | Ok _ => validate_types rest
          end
      end
  in
  let fix validate_entries
      (seen_keys : list type)
      (entries : list (type * type))
      : result unit :=
      match entries with
      | [] => Ok tt
      | (key, value) :: rest =>
          if contains_hole key then
            Err (TypeErr_HoleInMapPatternKey key)
          else if type_mem key seen_keys then
            Err (TypeErr_DuplicateMapPatternKey key)
          else
            match validate_map_pattern_keys key with
            | Err e => Err e
            | Ok _ =>
                match validate_map_pattern_keys value with
                | Err e => Err e
                | Ok _ => validate_entries (key :: seen_keys) rest
                end
            end
      end
  in
  match T with
  | T_Hole _ => Ok tt
  | T_Abbr _ => Ok tt
  | T_Elem _ => Ok tt
  | T_Prim _ => Ok tt
  | T_TRep T1 => validate_map_pattern_keys T1
  | T_Prod Ts => validate_types Ts
  | T_Comb _ Ts => validate_types Ts
  | T_Map entries => validate_entries [] entries
  end.

Definition valid_map_pattern_keys (T : type) : bool :=
  match validate_map_pattern_keys T with
  | Ok _ => true
  | Err _ => false
  end.

Fixpoint validate_map_pattern_keys_list
    (Ts : list type)
  : result unit :=
  match Ts with
  | [] => Ok tt
  | T :: rest =>
      match validate_map_pattern_keys T with
      | Err e => Err e
      | Ok _ => validate_map_pattern_keys_list rest
      end
  end.

Fixpoint find_duplicate_map_key
    (seen_keys : list type)
    (entries : list (type * type))
  : option type :=
  match entries with
  | [] => None
  | (key, _) :: rest =>
      if type_mem key seen_keys then
        Some key
      else
        find_duplicate_map_key (key :: seen_keys) rest
  end.

Fixpoint expr_beq (e1 e2 : expr) : bool :=
  match e1, e2 with
  | E_Var X, E_Var Y => eqb X Y
  | E_Elem x, E_Elem y => eqb x y
  | E_Prim p1, E_Prim p2 => prim_beq p1 p2
  | E_TRep T1, E_TRep T2 => type_beq T1 T2
  | E_Prod es1, E_Prod es2 => list_eqb expr_beq es1 es2
  | E_Comb ctor1 args1, E_Comb ctor2 args2 => 
      expr_beq ctor1 ctor2
      && list_eqb expr_beq args1 args2
  | E_Map lst1, E_Map lst2 =>
      permutation_eqb (pair_eqb expr_beq expr_beq) lst1 lst2
  | E_App a1 b1, E_App a2 b2 =>
      expr_beq a1 a2 && expr_beq b1 b2
  | _, _ =>
      false
  end.

Fixpoint type_comb_lookup
    (Gamma : type_context)
    (ctor : type)
    {struct Gamma}
  : option (TypeName * type * list string * list type) :=
  match Gamma with
  | [] => None
  | BindCombType TN defctor holenames defargs :: rest =>
      if type_beq ctor defctor then
        Some (TN, defctor, holenames, defargs)
      else
        type_comb_lookup rest ctor
  | _ :: rest => type_comb_lookup rest ctor
  end.

Fixpoint infer_list
    {A : Type}
    (f : type_context -> A -> result type)
    (Gamma : type_context)
    (ts : list A)
    {struct ts}
  : result (list type) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      match f Gamma t with
      | Err e => Err e
      | Ok T =>
          match infer_list f Gamma rest with
          | Err e => Err e
          | Ok Ts => Ok (T :: Ts)
          end
      end
  end.

Fixpoint comb_type_declared (Gamma : type_context) (TN : TypeName) : bool :=
  match Gamma with
  | [] => false
  | BindCombType TN' _ _ _ :: rest =>
      if eqb TN TN' then true else comb_type_declared rest TN
  | _ :: rest => comb_type_declared rest TN
  end.

Definition type_abbr_declared (Gamma : type_context) (TN : TypeName) : bool :=
  match type_abbr_lookup Gamma TN with
  | Some _ => true
  | None => false
  end.

Fixpoint comb_type_closed (Gamma : type_context) (TN : TypeName) : bool :=
  match Gamma with
  | [] => false
  | CloseCombType TN' :: rest =>
      if eqb TN TN' then true else comb_type_closed rest TN
  | _ :: rest => comb_type_closed rest TN
  end.

Definition type_declared (Gamma : type_context) (TN : TypeName) : bool :=
  comb_type_declared Gamma TN || type_abbr_declared Gamma TN.

Fixpoint norm_type_fuel
    (fuel : nat)
    (Gamma : type_context)
    (T : type)
  : result type :=
  match fuel with
  | 0 => Err TypeErr_InvalidType
  | S fuel' =>
      let fix norm_types (Ts : list type) : result (list type) :=
          match Ts with
          | [] => Ok []
          | T1 :: rest =>
              match norm_type_fuel fuel' Gamma T1 with
              | Err e => Err e
              | Ok T1N =>
                  match norm_types rest with
                  | Err e => Err e
                  | Ok restN => Ok (T1N :: restN)
                  end
              end
          end
      in
      let fix norm_map_entries
          (entries : list (type * type))
          : result (list (type * type)) :=
          match entries with
          | [] => Ok []
          | (K, V) :: rest =>
              match norm_type_fuel fuel' Gamma K with
              | Err e => Err e
              | Ok KN =>
                  match norm_type_fuel fuel' Gamma V with
                  | Err e => Err e
                  | Ok VN =>
                      match norm_map_entries rest with
                      | Err e => Err e
                      | Ok restN => Ok ((KN, VN) :: restN)
                      end
                  end
              end
          end
      in
      match T with
      | T_Hole X => Ok (T_Hole X)
      | T_Elem e => Ok (T_Elem e)
      | T_Prim p => Ok (T_Prim p)
      | T_Abbr X =>
          match type_abbr_lookup Gamma X with
          | None => Err (Err_UnboundTypeAbbr X)
          | Some T' => norm_type_fuel fuel' Gamma T'
          end
      | T_TRep T1 =>
          match norm_type_fuel fuel' Gamma T1 with
          | Err e => Err e
          | Ok T1N => Ok (T_TRep T1N)
          end
      | T_Prod Ts =>
          match norm_types Ts with
          | Err e => Err e
          | Ok [] => Ok T_Unit
          | Ok [T1] => Err (TypeErr_InvalidProd T1)
          | Ok TsN => Ok (T_Prod TsN)
          end
      | T_Comb X Ts =>
          match norm_types Ts with
          | Err e => Err e
          | Ok TsN => Ok (T_Comb X TsN)
          end
      | T_Map entries =>
          match norm_map_entries entries with
          | Err e => Err e
          | Ok entriesN => Ok (T_Map entriesN)
          end
      end
  end.

Definition norm_type (Gamma : type_context) (T : type) : result type :=
  norm_type_fuel (S (type_size T + type_context_size Gamma)) Gamma T.

Fixpoint norm_list (Gamma : type_context) (ts : list type) : result (list type) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      match norm_type Gamma t with
      | Err e => Err e
      | Ok tN =>
          match norm_list Gamma rest with
          | Err e => Err e
          | Ok restN => Ok (tN :: restN)
          end
      end
  end.

Fixpoint norm_comb_list
    (Gamma : type_context)
    (ts : list type)
  : result (list type) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      match norm_type Gamma t with
      | Err e => Err e
      | Ok tN =>
          if contains_prim tN then
            Err (TypeErr_UsePrimInDeclComb tN)
          else
            match norm_comb_list Gamma rest with
            | Err e => Err e
            | Ok restN => Ok (tN :: restN)
            end
      end
  end.

Definition norm_type_beq
    (Gamma : type_context)
    (T1 T2 : type)
  : result bool :=
  match norm_type Gamma T1 with
  | Err e => Err e
  | Ok N1 =>
      match norm_type Gamma T2 with
      | Err e => Err e
      | Ok N2 => Ok (type_beq N1 N2)
      end
  end.

Fixpoint value_beq (v1 v2 : value) : bool :=
  match v1, v2 with
  | V_Elem e1, V_Elem e2 => eqb e1 e2
  | V_Prim p1, V_Prim p2 => prim_beq p1 p2
  | V_TRep T1, V_TRep T2 => type_beq T1 T2
  | V_Prod vs1, V_Prod vs2 => list_eqb value_beq vs1 vs2
  | V_Comb ctor1 args1, V_Comb ctor2 args2 =>
      value_beq ctor1 ctor2 && list_eqb value_beq args1 args2
  | V_Map lst1, V_Map lst2 =>
      permutation_eqb (pair_eqb value_beq value_beq) lst1 lst2
  | _, _ =>
      false
  end.

Definition type_subst : Type := list (string * type).

Fixpoint type_hole_lookup (subst : type_subst) (X : string) : option type :=
  match subst with
  | [] => None
  | (Y, T) :: rest =>
      if eqb X Y then Some T else type_hole_lookup rest X
  end.

Fixpoint unify_type_fuel
    (fuel : nat)
    (subst : type_subst)
    (ptrn actual : type)
  : result type_subst :=
  let fix unify_list_elements
      (fuel' : nat)
      (ptrns_orig actuals_orig : list type)
      (subst0 : type_subst)
      (ptrns0 actuals0 : list type)
      {struct ptrns0}
      : result type_subst :=
      match ptrns0, actuals0 with
      | [], [] => Ok subst0
      | ptrn0 :: ptrn_rest, actual0 :: actual_rest =>
          match unify_type_fuel fuel' subst0 ptrn0 actual0 with
          | Err e => Err e
          | Ok subst1 => 
              unify_list_elements 
                  fuel' ptrns_orig actuals_orig subst1 ptrn_rest actual_rest
          end
      | _, _ => Err (TypeErr_ListMismatch ptrns_orig actuals_orig)
      end
  in
  let fix find_and_remove_map_entry
      (ptrn_key : type)
      (actual_entries : list (type * type))
      {struct actual_entries}
      : option (type * list (type * type)) :=
      match actual_entries with
      | [] =>
          None
      | (actual_key, actual_value) :: actual_rest =>
          if type_beq ptrn_key actual_key then
            Some (actual_value, actual_rest)
          else
            match
              find_and_remove_map_entry
                ptrn_key
                actual_rest
            with
            | None =>
                None
            | Some (found_value, remaining_entries) =>
                Some
                  (found_value,
                   (actual_key, actual_value)
                     :: remaining_entries)
            end
      end
  in
  let fix unify_map_entries
      (fuel' : nat)
      (ptrn_map_orig actual_map_orig :
         list (type * type))
      (subst0 : type_subst)
      (ptrn_entries actual_entries :
         list (type * type))
      {struct ptrn_entries}
      : result type_subst :=
      match ptrn_entries with
      | [] =>
          Ok subst0
      | (ptrn_key, ptrn_value) :: ptrn_rest =>
          if contains_hole ptrn_key then
            Err (TypeErr_HoleInMapPatternKey ptrn_key)
          else
            match
              find_and_remove_map_entry
                ptrn_key
                actual_entries
            with
            | None =>
                Err
                  (TypeErr_Mismatch
                     (T_Map ptrn_map_orig)
                     (T_Map actual_map_orig))
            | Some (actual_value, actual_rest) =>
                match
                  unify_type_fuel
                    fuel'
                    subst0
                    ptrn_value
                    actual_value
                with
                | Err e =>
                    Err e
                | Ok subst1 =>
                    unify_map_entries
                      fuel'
                      ptrn_map_orig
                      actual_map_orig
                      subst1
                      ptrn_rest
                      actual_rest
                end
            end
      end
  in
  match fuel with
  | 0 => Err TypeErr_InvalidType
  | S fuel' =>
    if contains_hole actual then
      Err (TypeErr_UseHole actual)
    else
      match ptrn with
      | T_Hole X =>
          match type_hole_lookup subst X with
          | Some T =>
              if type_beq T actual then
                Ok subst
              else
                Err (TypeErr_Mismatch T actual)
          | None => Ok ((X, actual) :: subst)
          end
      | T_Abbr X =>
          match actual with
          | T_Abbr Y =>
              if eqb X Y then
                Ok subst
              else
                Err (TypeErr_Mismatch ptrn actual)
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | T_Elem e1 =>
          match actual with
          | T_Elem e2 =>
              if eqb e1 e2 then
                Ok subst
              else
                Err (TypeErr_Mismatch ptrn actual)
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | T_Prim p1 =>
          match actual with
          | T_Prim p2 =>
              if prim_beq p1 p2 then
                Ok subst
              else
                Err (TypeErr_Mismatch ptrn actual)
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | T_TRep ptrn1 =>
          match actual with
          | T_TRep actual1 =>
              unify_type_fuel fuel' subst ptrn1 actual1
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | T_Prod ptrn_args =>
          match actual with
          | T_Prod actual_args => 
                unify_list_elements 
                  fuel' ptrn_args actual_args subst ptrn_args actual_args
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | T_Comb ptrn_name ptrn_args =>
          match actual with
          | T_Comb actual_name actual_args =>
              if eqb ptrn_name actual_name then
                unify_list_elements 
                  fuel' ptrn_args actual_args subst ptrn_args actual_args
              else
                Err (TypeErr_Mismatch ptrn actual)
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | T_Map ptrn_entries =>
            match actual with
            | T_Map actual_entries =>
                match find_duplicate_map_key [] ptrn_entries with
                | Some duplicate_key =>
                    Err (TypeErr_DuplicateMapPatternKey duplicate_key)
                | None =>
                    match find_duplicate_map_key [] actual_entries with
                    | Some duplicate_key => 
                        Err (TypeErr_DuplicateMapKey duplicate_key)
                    | None =>
                        unify_map_entries
                          fuel'
                          ptrn_entries
                          actual_entries
                          subst
                          ptrn_entries
                          actual_entries
                    end
                end
            | _ => Err (TypeErr_Mismatch ptrn actual)
            end
      end
  end.

Definition unify_type
    (subst : type_subst)
    (ptrn actual : type)
  : result type_subst :=
  unify_type_fuel (S (type_size ptrn)) subst ptrn actual.

Fixpoint unify_type_list_aux
    (subst : type_subst)
    (ptrns actuals : list type)
    (original_ptrns original_actuals : list type)
    {struct ptrns}
  : result type_subst :=
  match ptrns, actuals with
  | [], [] => Ok subst
  | ptrn :: ptrn_rest, actual :: actual_rest =>
      match unify_type subst ptrn actual with
      | Err e => Err e
      | Ok subst' =>
          unify_type_list_aux
            subst'
            ptrn_rest
            actual_rest
            original_ptrns
            original_actuals
      end
  | _, _ =>
      Err
        (TypeErr_ListMismatch
           original_ptrns
           original_actuals)
  end.

Definition unify_type_list
    (subst : type_subst)
    (ptrns actuals : list type)
  : result type_subst :=
  unify_type_list_aux
    subst
    ptrns
    actuals
    ptrns
    actuals.

Definition unify_generic_list
    (plst arglst : list type)
  : result (list type) :=
  match unify_type_list [] plst arglst with
  | Ok _ => Ok arglst
  | Err e => Err e
  end.

Fixpoint holenames_in_subst_lookup
    (holenames : list string)
    (subst : type_subst)
  : result (list type) :=
  match holenames with
  | [] => Ok []
  | X :: rest =>
      match type_hole_lookup subst X with
      | None => Err (Err_UnboundHole X)
      | Some T =>
          match holenames_in_subst_lookup rest subst with
          | Err e => Err e
          | Ok Ts => Ok (T :: Ts)
          end
      end
  end.

Definition infer_comb_type_decl_info
      (f : type_context -> expr -> result type)
      (Gamma0 : type_context)
      (ctor : expr)
      : result (TypeName * type * list string * list type) :=
      match f Gamma0 ctor with
      | Err e => Err e
      | Ok ctortype =>
          match type_comb_lookup Gamma0 ctortype with
          | None => Err TypeErr_UnknownCombSignature
          | Some (tn, declared_ctor_type, holenames, argsptrn) =>
              Ok (tn, declared_ctor_type, holenames, argsptrn)
          end
      end.

Definition infer_comb_type_info
      (f : type_context -> expr -> result type)
      (Gamma0 : type_context)
      (ctor : expr)
      (arglst : list expr)
      : result (TypeName * type * list type) :=
      match infer_comb_type_decl_info f Gamma0 ctor with
      | Err e => Err e
      | Ok (tn, ctortype, holenames, argsptrn) =>
          match infer_list f Gamma0 arglst with
          | Err e => Err e
          | Ok argtypes =>
              match unify_type_list [] argsptrn argtypes with
              | Err e => Err e
              | Ok argsubst =>
                  match
                    holenames_in_subst_lookup holenames argsubst
                  with
                  | Err e => Err e
                  | Ok typeargs => Ok (tn, ctortype, typeargs)
                  end
              end
          end
      end.

Definition infer_comb_prim_app
      (f : type_context -> expr -> result type)
      (Gamma : type_context)
      (ctor : expr)
      (arglst : list expr)
      (prm : prim)
      : result type :=
      match infer_comb_type_info f Gamma ctor arglst with
      | Err e => Err e
      | Ok _ =>
          match f Gamma ctor with
          | Err e => Err e
          | Ok ctortype =>
              match infer_list f Gamma arglst with
              | Err e => Err e
              | Ok argtypes =>
                  match prm with
                  | Prm_Left => norm_type Gamma ctortype
                  | Prm_Right =>
                      match argtypes with
                      | [] => Ok T_Unit
                      | [x] => norm_type Gamma x
                      | xs => norm_type Gamma (T_Prod xs)
                      end
                  end
              end
          end
      end.

Definition infer_type_app
    (f : type_context -> expr -> result type)
    (Gamma : type_context)
    (a b : expr)
    (aty bty : type)
  : result type :=
  match a, aty, b, bty with
  | E_Comb ctor arglst, _, (E_Prim prm), _ =>
      infer_comb_prim_app f Gamma ctor arglst prm
  | _, T_Prod [], _, T_Prim _ => Err (TypeErr_InvalidApp aty bty)
  | _, T_Prod (x :: _), _, T_Prim Prm_Left => norm_type Gamma x
  | _, T_Prod xs, _, T_Prim Prm_Right => norm_type Gamma (last xs T_Unit)
  | _, _, _, _ => Err (TypeErr_InvalidApp aty bty)
  end.

Fixpoint expr_key_mem
    (key : expr)
    (keys : list expr)
  : bool :=
  match keys with
  | [] => false
  | key' :: rest => expr_beq key key' || expr_key_mem key rest
  end.
  
Fixpoint value_key_mem
    (key : value)
    (keys : list value)
  : bool :=
  match keys with
  | [] =>
      false
  | key' :: rest => value_beq key key' || value_key_mem key rest
  end.

Fixpoint infer_type_expr
    (Gamma : type_context)
    (tm : expr)
    {struct tm}
  : result type :=
  let fix infer_map_entries
    (seen_key_types : list type)
    (entries : list (expr * expr))
    : result (list (type * type)) :=
    match entries with
    | [] => Ok []
    | (key, val) :: rest =>
        match infer_type_expr Gamma key with
        | Err e => Err e
        | Ok key_type =>
            match norm_type Gamma key_type with
            | Err e => Err e
            | Ok normalized_key_type =>
                if type_mem normalized_key_type seen_key_types
                then Err (TypeErr_DuplicateMapKey normalized_key_type)
                else
                  match infer_type_expr Gamma val with
                  | Err e => Err e
                  | Ok value_type =>
                      match norm_type Gamma value_type with
                      | Err e => Err e
                      | Ok normalized_value_type =>
                          match
                            infer_map_entries 
                              (normalized_key_type :: seen_key_types) rest
                          with
                          | Err e => Err e
                          | Ok rest_types =>
                              Ok
                                ((normalized_key_type,
                                  normalized_value_type)
                                 :: rest_types)
                          end
                      end
                  end
            end
        end
    end
  in
  match tm with
  | E_Var X => Err (Err_UnexpandedVar X)
  | E_Elem e => Ok (T_Elem e)
  | E_Prim p => Ok (T_Prim p)
  | E_TRep T =>
      match norm_type Gamma (T_TRep T) with
      | Err e => Err e
      | Ok TN =>
          if contains_hole TN then
            Err (ExprErr_UseHole tm)
          else
            Ok TN
      end
  | E_Prod [] => Ok T_Unit
  | E_Prod [x] => Err (ExprErr_InvalidProd tm) 
  | E_Prod (x :: xs) =>
      match
        infer_list infer_type_expr Gamma (x :: xs)
      with
      | Err e => Err e
      | Ok Ts => norm_type Gamma (T_Prod Ts)
      end
  | E_Comb ctor arglst =>
      match infer_comb_type_info infer_type_expr Gamma ctor arglst with
      | Err e => Err e
      | Ok (tn, _, typeargs) =>
          let trep_replace (T : type) : type :=
              match T with
              | T_TRep T1 => T1
              | _ => T
              end
          in
          Ok (T_Comb tn (map trep_replace typeargs))
      end
  | E_Map entries =>
      match infer_map_entries [] entries with
      | Err e => Err e
      | Ok entry_types => Ok (T_Map entry_types)
      end
  | E_App a b =>
      match infer_type_expr Gamma a with
      | Err e => Err e
      | Ok ta =>
          match infer_type_expr Gamma b with
          | Err e => Err e
          | Ok tb =>  infer_type_app infer_type_expr Gamma a b ta tb
          end 
      end
  end.

Fixpoint eval_expr
    (tm : expr)
    {struct tm}
  : result value :=
  match tm with
  | E_Var X => Err (Err_UnexpandedVar X)
  | E_Elem e => Ok (V_Elem e)
  | E_Prim p => Ok (V_Prim p)
  | E_TRep T =>
      match norm_type [] T with
      | Err e => Err e
      | Ok TN => Ok (V_TRep TN)
      end
  | E_Prod es =>
      match es with
      | [] => Ok V_Unit
      | [e] => Err (ExprErr_InvalidProd tm)
      | _ =>
          match eval_expr_list eval_expr es with
          | Err e => Err e
          | Ok vs => Ok (V_Prod vs)
          end
      end
  | E_Comb ctor args =>
      match eval_expr ctor with
      | Err e => Err e
      | Ok ctor_value =>
          match eval_expr_list eval_expr args with
          | Err e => Err e
          | Ok arg_values =>
              Ok (V_Comb ctor_value arg_values)
          end
      end
  | E_Map entries =>
      let fix eval_map_entries
          (seen_keys : list value)
          (xs : list (expr * expr))
          : result (list (value * value)) :=
          match xs with
          | [] => Ok []
          | (key_expr, val_expr) :: rest =>
              match eval_expr key_expr with
              | Err e => Err e
              | Ok key_value =>
                  if value_key_mem key_value seen_keys then
                    Err (ExprErr_DuplicateMapKey key_expr)
                  else
                    match eval_expr val_expr with
                    | Err e => Err e
                    | Ok val_value =>
                        match eval_map_entries (key_value :: seen_keys) rest with
                        | Err e => Err e
                        | Ok rest_values =>
                            Ok ((key_value, val_value) :: rest_values)
                        end
                    end
              end
          end
      in
      match eval_map_entries [] entries with
      | Err e =>
          Err e
      | Ok values =>
          Ok (V_Map values)
      end
  | E_App a b =>
      match eval_expr a with
      | Err e => Err e
      | Ok va =>
          match eval_expr b with
          | Err e => Err e
          | Ok vb =>
              match va, vb with
              | V_Prod [], V_Prim _ =>
                  Err (ExprErr_InvalidApp a b)
              | V_Prod (x :: _), V_Prim Prm_Left => Ok x
              | V_Prod xs, V_Prim Prm_Right =>
                  Ok (last xs V_Unit)
              | V_Comb ctor _, V_Prim Prm_Left => Ok ctor
              | V_Comb _ args, V_Prim Prm_Right =>
                  match args with
                  | [] => Ok V_Unit
                  | [x] => Ok x
                  | xs => Ok (V_Prod xs)
                  end
              | _, _ => Err (ExprErr_InvalidApp a b)
              end
          end
      end
  end.

Fixpoint type_contains_named_hole
    (X : string)
    (T : type)
  : bool :=
  match T with
  | T_Hole Y => eqb X Y
  | T_Abbr _ => false
  | T_Elem _ => false
  | T_Prim _ => false
  | T_TRep T1 =>
      type_contains_named_hole X T1
  | T_Prod Ts =>
      existsb (type_contains_named_hole X) Ts
  | T_Comb _ Ts =>
      existsb (type_contains_named_hole X) Ts
  | T_Map entries =>
      existsb
        (fun entry =>
           let '(K, V) := entry in
           type_contains_named_hole X K
           || type_contains_named_hole X V)
        entries
  end.

Definition hole_occurs_in_types
    (X : string)
    (Ts : list type)
  : bool :=
  existsb (type_contains_named_hole X) Ts.

Fixpoint validate_declared_holes_used
    (holenames : list string)
    (args : list type)
  : result unit :=
  match holenames with
  | [] =>
      Ok tt
  | X :: rest =>
      if hole_occurs_in_types X args then
        validate_declared_holes_used rest args
      else
        Err (TypeErr_DeclaredHoleNotUsed X)
  end.

Definition holename_mem
    (X : string)
    (holenames : list string)
  : bool :=
  existsb (fun Y => eqb X Y) holenames.

Fixpoint validate_type_holes_declared
    (holenames : list string)
    (T : type)
  : result unit :=
  let fix validate_types (Ts : list type) : result unit :=
      match Ts with
      | [] => Ok tt
      | T1 :: rest =>
          match
            validate_type_holes_declared holenames T1 with
          | Err e => Err e
          | Ok _ => validate_types rest
          end
      end
  in
  let fix validate_entries (entries : list (type * type)) : result unit :=
      match entries with
      | [] => Ok tt
      | (K, V) :: rest =>
          match validate_type_holes_declared holenames K with
          | Err e => Err e
          | Ok _ =>
              match validate_type_holes_declared holenames V with
              | Err e => Err e
              | Ok _ => validate_entries rest
              end
          end
      end
  in
  match T with
  | T_Hole X =>
      if holename_mem X holenames then
        Ok tt
      else
        Err (TypeErr_UndeclaredHole X)
  | T_Abbr _ => Ok tt
  | T_Elem _ => Ok tt
  | T_Prim _ => Ok tt
  | T_TRep T1 => validate_type_holes_declared holenames T1
  | T_Prod Ts => validate_types Ts
  | T_Comb _ Ts => validate_types Ts
  | T_Map entries => validate_entries entries
  end.

Fixpoint validate_argument_holes_declared
    (holenames : list string)
    (args : list type)
  : result unit :=
  match args with
  | [] => Ok tt
  | T :: rest =>
      match validate_type_holes_declared holenames T with
      | Err e => Err e
      | Ok _ => validate_argument_holes_declared holenames rest
      end
  end.

Fixpoint validate_unique_holenames_aux
    (seen : list string)
    (holenames : list string)
  : result unit :=
  match holenames with
  | [] =>
      Ok tt
  | X :: rest =>
      if holename_mem X seen then
        Err (TypeErr_DuplicateHoleName X)
      else
        validate_unique_holenames_aux
          (X :: seen)
          rest
  end.

Definition validate_unique_holenames (holenames : list string)
  : result unit :=
  validate_unique_holenames_aux [] holenames.

Definition validate_hole_declaration (holenames : list string) (args : list type)
  : result unit :=
  match validate_unique_holenames holenames with
  | Err e => Err e
  | Ok _ =>
      match validate_declared_holes_used holenames args with
      | Err e => Err e
      | Ok _ => validate_argument_holes_declared holenames args
      end
  end.

Definition exec_command
    (st : machine_state)
    (cmd : command)
  : result machine_state :=
  let Gamma := ms_type_ctx st in
  match cmd with
  | C_DeclVar _ rhs =>
      match infer_type_expr Gamma rhs with
      | Err e => Err e
      | Ok _ => Ok st
      end
  | C_NewTypeAbbr X T =>
      if type_declared Gamma X then
        Err (TypeErr_DuplicateType X)
      else
        match norm_type Gamma T with
        | Err e => Err e
        | Ok TN =>
            Ok
              {| ms_type_ctx := BindTypeAbbr X TN :: Gamma;
                 ms_last_type := ms_last_type st;
                 ms_last_value := ms_last_value st |}
        end
  | C_DeclCombVariant tn ctortype holenames args =>
      if comb_type_closed Gamma tn then
        Err (TypeErr_CombClosed tn)
      else if type_abbr_declared Gamma tn then
        Err (TypeErr_DuplicateType tn)
      else
        match norm_type Gamma ctortype with
        | Err e => Err e
        | Ok nrmctortype =>
            if contains_hole nrmctortype then
              Err (TypeErr_UseHole nrmctortype)
            else
            if contains_prim nrmctortype then
              Err (TypeErr_UsePrimInDeclComb nrmctortype)
            else
              match validate_map_pattern_keys nrmctortype with
              | Err e => Err e
              | Ok _ =>
                  match type_comb_lookup Gamma nrmctortype with
                  | Some (oldtn, _, _, _) =>
                      Err (TypeErr_DuplicateCombSignature oldtn nrmctortype)
                  | None =>
                      match norm_comb_list Gamma args with
                      | Err e => Err e
                      | Ok nrmargs =>
                          match validate_hole_declaration holenames nrmargs with
                          | Err e => Err e
                          | Ok _ =>
                            match validate_map_pattern_keys_list nrmargs with
                            | Err e => Err e
                            | Ok _ =>
                                Ok
                                  {| ms_type_ctx :=
                                       BindCombType tn nrmctortype holenames nrmargs 
                                       :: Gamma;
                                     ms_last_type := ms_last_type st;
                                     ms_last_value := ms_last_value st |}
                            end
                          end
                      end
                  end
              end
        end
  | C_Eval e =>
      match infer_type_expr Gamma e with
      | Err er => Err er
      | Ok T =>
          match eval_expr e with
          | Err er => Err er
          | Ok v =>
              Ok
                {| ms_type_ctx := Gamma;
                   ms_last_type := T;
                   ms_last_value := v |}
          end
      end
  | C_CloseCombType tn =>
      if negb (comb_type_declared Gamma tn) then
        Err (TypeErr_CloseUnknownComb tn)
      else if comb_type_closed Gamma tn then
        Err (TypeErr_CombAlreadyClosed tn)
      else
        Ok
          {| ms_type_ctx := CloseCombType tn :: Gamma;
             ms_last_type := ms_last_type st;
             ms_last_value := ms_last_value st |}
  end.

Definition prog : Type := list command.
Definition type_def_context : Type := list (TypeName * type).
Definition expr_def_context : Type := list (VarName * expr).

Fixpoint lookup_type_def
    (Delta : type_def_context)
    (X : TypeName)
  : option type :=
  match Delta with
  | [] => None
  | (Y, T) :: rest =>
      if eqb X Y then Some T else lookup_type_def rest X
  end.

Fixpoint lookup_expr_def
    (Sigma : expr_def_context)
    (X : VarName)
  : option expr :=
  match Sigma with
  | [] => None
  | (Y, tm) :: rest =>
      if eqb X Y then Some tm else lookup_expr_def rest X
  end.

Definition expr_def_declared
    (Sigma : expr_def_context)
    (X : VarName)
  : bool :=
  match lookup_expr_def Sigma X with
  | Some _ => true
  | None => false
  end.

Definition type_def_declared
    (Delta : type_def_context)
    (X : TypeName)
  : bool :=
  match lookup_type_def Delta X with
  | Some _ => true
  | None => false
  end.

Fixpoint unfold_type
    (Delta : type_def_context)
    (T : type)
    {struct T}
  : result type :=
  match T with
  | T_Abbr X =>
      match lookup_type_def Delta X with
      | None => Err (Err_UnboundTypeAbbr X)
      | Some T' => Ok T'
      end
  | T_Hole X => Ok (T_Hole X)
  | T_Elem e => Ok (T_Elem e)
  | T_Prim p => Ok (T_Prim p)
  | T_TRep T1 =>
      match unfold_type Delta T1 with
      | Err e => Err e
      | Ok T1' => Ok (T_TRep T1')
      end
  | T_Prod Ts =>
      let fix unfold_types
          (xs : list type)
          : result (list type) :=
          match xs with
          | [] => Ok []
          | x :: rest =>
              match unfold_type Delta x with
              | Err e => Err e
              | Ok x' =>
                  match unfold_types rest with
                  | Err e => Err e
                  | Ok rest' => Ok (x' :: rest')
                  end
              end
          end
      in
      match unfold_types Ts with
      | Err e => Err e
      | Ok Ts' => Ok (T_Prod Ts')
      end
  | T_Comb tn Ts =>
      let fix unfold_types
          (xs : list type)
          : result (list type) :=
          match xs with
          | [] => Ok []
          | x :: rest =>
              match unfold_type Delta x with
              | Err e => Err e
              | Ok x' =>
                  match unfold_types rest with
                  | Err e => Err e
                  | Ok rest' => Ok (x' :: rest')
                  end
              end
          end
      in
      match unfold_types Ts with
      | Err e => Err e
      | Ok Ts' => Ok (T_Comb tn Ts')
      end
  | T_Map entries =>
    let fix unfold_entries
        (xs : list (type * type))
        : result (list (type * type)) :=
        match xs with
        | [] => Ok []
        | (K, V) :: rest =>
            match unfold_type Delta K with
            | Err e => Err e
            | Ok K' =>
                match unfold_type Delta V with
                | Err e => Err e
                | Ok V' =>
                    match unfold_entries rest with
                    | Err e => Err e
                    | Ok rest' =>
                        Ok ((K', V') :: rest')
                    end
                end
            end
        end
    in
    match unfold_entries entries with
    | Err e => Err e
    | Ok entries' => Ok (T_Map entries')
    end
  end.

Fixpoint unfold_expr
    (Sigma : expr_def_context)
    (Delta : type_def_context)
    (tm : expr)
    {struct tm}
  : result expr :=
  match tm with
  | E_Var X =>
      match lookup_expr_def Sigma X with
      | None => Err (Err_UnboundVar X)
      | Some tm' => Ok tm'
      end
  | E_Elem e => Ok (E_Elem e)
  | E_Prim p => Ok (E_Prim p)
  | E_TRep T =>
      match unfold_type Delta T with
      | Err e => Err e
      | Ok T' => Ok (E_TRep T')
      end
  | E_Prod es =>
      let fix unfold_exprs
          (xs : list expr)
          : result (list expr) :=
          match xs with
          | [] => Ok []
          | x :: rest =>
              match unfold_expr Sigma Delta x with
              | Err e => Err e
              | Ok x' =>
                  match unfold_exprs rest with
                  | Err e => Err e
                  | Ok rest' => Ok (x' :: rest')
                  end
              end
          end
      in
      match unfold_exprs es with
      | Err e => Err e
      | Ok es' => Ok (E_Prod es')
      end
  | E_Comb ctor args =>
      match unfold_expr Sigma Delta ctor with
      | Err e => Err e
      | Ok ctor' =>
          let fix unfold_exprs
              (xs : list expr)
              : result (list expr) :=
              match xs with
              | [] => Ok []
              | x :: rest =>
                  match unfold_expr Sigma Delta x with
                  | Err e => Err e
                  | Ok x' =>
                      match unfold_exprs rest with
                      | Err e => Err e
                      | Ok rest' => Ok (x' :: rest')
                      end
                  end
              end
          in
          match unfold_exprs args with
          | Err e => Err e
          | Ok args' => Ok (E_Comb ctor' args')
          end
      end
  | E_Map entries =>
    let fix unfold_entries (xs : list (expr * expr)) : result (list (expr * expr)) :=
        match xs with
        | [] => Ok []
        | (key, val) :: rest =>
            match unfold_expr Sigma Delta key with
            | Err e => Err e
            | Ok key' =>
                match unfold_expr Sigma Delta val with
                | Err e => Err e
                | Ok val' =>
                    match unfold_entries rest with
                    | Err e => Err e
                    | Ok rest' => Ok ((key', val') :: rest')
                    end
                end
            end
        end
    in
    match unfold_entries entries with
    | Err e => Err e
    | Ok entries' => Ok (E_Map entries')
    end
  | E_App a b =>
      match unfold_expr Sigma Delta a with
      | Err e => Err e
      | Ok a' =>
          match unfold_expr Sigma Delta b with
          | Err e => Err e
          | Ok b' => Ok (E_App a' b')
          end
      end
  end.

Fixpoint unfold_prog_aux
    (Sigma : expr_def_context)
    (Delta : type_def_context)
    (prg : prog)
    {struct prg}
  : result prog :=
  match prg with
  | [] => Ok []
  | C_DeclVar X rhs :: rest =>
      if expr_def_declared Sigma X then
        Err (Err_DuplicateVar X)
      else
        match unfold_expr Sigma Delta rhs with
        | Err e => Err e
        | Ok rhs' =>
            unfold_prog_aux
              ((X, rhs') :: Sigma)
              Delta
              rest
        end
  | C_NewTypeAbbr X T :: rest =>
      if type_def_declared Delta X then
        Err (TypeErr_DuplicateType X)
      else
        match unfold_type Delta T with
        | Err e => Err e
        | Ok T' =>
            match
              unfold_prog_aux
                Sigma
                ((X, T') :: Delta)
                rest
            with
            | Err e => Err e
            | Ok rest' =>
                Ok (C_NewTypeAbbr X T' :: rest')
            end
        end
  | C_DeclCombVariant tn ctor holenames args :: rest =>
      match unfold_type Delta ctor with
      | Err e => Err e
      | Ok ctor' =>
          let fix unfold_types
              (xs : list type)
              : result (list type) :=
              match xs with
              | [] => Ok []
              | x :: xs' =>
                  match unfold_type Delta x with
                  | Err e => Err e
                  | Ok x' =>
                      match unfold_types xs' with
                      | Err e => Err e
                      | Ok rest' => Ok (x' :: rest')
                      end
                  end
              end
          in
          match unfold_types args with
          | Err e => Err e
          | Ok args' =>
              match
                unfold_prog_aux Sigma Delta rest
              with
              | Err e => Err e
              | Ok rest' =>
                  Ok
                    (C_DeclCombVariant
                       tn
                       ctor'
                       holenames
                       args'
                     :: rest')
              end
          end
      end
  | C_Eval e :: rest =>
      match unfold_expr Sigma Delta e with
      | Err er => Err er
      | Ok e' =>
          match unfold_prog_aux Sigma Delta rest with
          | Err er => Err er
          | Ok rest' => Ok (C_Eval e' :: rest')
          end
      end
  | C_CloseCombType tn :: rest =>
      match unfold_prog_aux Sigma Delta rest with
      | Err e => Err e
      | Ok rest' => Ok (C_CloseCombType tn :: rest')
      end
  end.

Definition unfold_prog (prg : prog) : result prog :=
  unfold_prog_aux [] [] prg.

Record Prg_Result : Type := {
  prog_type : type;
  prog_val : value
}.

Fixpoint run_prog_aux
    (st : machine_state)
    (prg : prog)
    {struct prg}
  : result machine_state :=
  match prg with
  | [] => Ok st
  | cmd :: rest =>
      match exec_command st cmd with
      | Err e => Err e
      | Ok st' => run_prog_aux st' rest
      end
  end.

Definition run_prog
    (input_program : prog)
  : result Prg_Result :=
  match unfold_prog input_program with
  | Err e => Err e
  | Ok unfolded_program =>
      match
        run_prog_aux initial_state unfolded_program
      with
      | Err e => Err e
      | Ok st =>
          Ok
            {| prog_type := ms_last_type st;
               prog_val := ms_last_value st |}
      end
  end.

(* Тривиальный пример хорошей программы *)
Example example_good_prog0 := [
  C_DeclVar "minprod" (E_Prod [E_Elem "bla"; E_Unit]); 
  C_DeclVar "myvar" (E_Prod [E_TRep (T_Elem "one"); E_Elem "0"; E_Elem "2"; E_Var "minprod"]);
  C_Eval (E_Prod [E_App (E_Var "myvar") (E_Prim Prm_Left); E_App (E_Var "myvar") (E_Prim Prm_Right)]) ].
Compute (run_prog example_good_prog0).

(* Хорошая программа -  объявление типов-комбинаций *)
Example example_good_prog2 := [
  C_DeclCombVariant "Bool" (T_Elem "true") [] [];
  C_DeclCombVariant "Bool" (T_Elem "false") [] [];
  C_CloseCombType "Bool";
  C_Eval (E_Comb (E_Elem "true") [])
].
Compute (run_prog example_good_prog2).

(* Хорошая программа -  объявление индуктивного типа натуральных чисел *)
Example example_good_prog3 := [
  C_DeclCombVariant "Option" (T_Elem "None") ["a"] [T_TRep (T_Hole "a")];
  C_DeclCombVariant "Option" (T_Elem "Some") ["a"] [T_Hole "a"];
  C_CloseCombType "Option";
  C_DeclCombVariant "Nat" (T_Elem "Zero") [] [];
  C_DeclCombVariant "Nat" (T_Elem "Succ") [] [T_Comb "Nat" []];
  C_CloseCombType "Nat";
  C_DeclVar "zero" (E_Comb (E_Elem "Zero") []);
  C_Eval (E_Comb (E_Elem "Some") [E_Comb (E_Elem "Succ") [E_Var "zero"]])
].
Compute (run_prog example_good_prog3).

(* Хорошая программа - типы комбинаций с параметрами произвольных типов *)
Example example_good_prog4 := [
  C_DeclCombVariant "Foo" (T_Elem "Foo") ["a"; "b"] [T_Hole "a"; T_Hole "b"];
  C_CloseCombType "Foo";
  C_Eval (E_Comb (E_Elem "Foo") [E_Unit; (E_Prim Prm_Left)])
].
Compute (run_prog example_good_prog4).

(* Хорошая программа - типы комбинаций с параметрами одинаковых типов *)
Example example_good_prog5 := [
  C_DeclCombVariant "Foo" (T_Elem "Foo") ["a"] [T_Hole "a"; T_Hole "a"];
  C_CloseCombType "Foo";
  C_Eval (E_Comb (E_Elem "Foo") [E_Unit; E_Unit])
].
Compute (run_prog example_good_prog5).

(* Хорошая программа -  применение E_Prim к комбинации *)
Example example_good_prog6 := [
  C_DeclCombVariant "Option" (T_Elem "None") ["a"] [T_TRep (T_Hole "a")];
  C_DeclCombVariant "Option" (T_Elem "Some") ["a"] [T_Hole "a"];
  C_CloseCombType "Option";
  C_DeclCombVariant "Nat" (T_Elem "Zero") [] [];
  C_DeclCombVariant "Nat" (T_Elem "Succ") [] [T_Comb "Nat" []];
  C_CloseCombType "Nat";
  C_DeclVar "zero" (E_Comb (E_Elem "Zero") []);
  C_DeclVar "comb" (E_Comb (E_Elem "Some") [E_Comb (E_Elem "Succ") [E_Var "zero"]]);
  C_Eval (E_App (E_Var "comb") (E_Prim Prm_Right))
].
Compute (run_prog example_good_prog6).

(* Хорошая программа - Тип списков *)
Example example_good_prog7 := [
  C_DeclCombVariant "Nat" (T_Elem "Zero") [] [];
  C_DeclCombVariant "Nat" (T_Elem "Succ") [] [T_Comb "Nat" []];
  C_CloseCombType "Nat";
  C_DeclCombVariant "List" (T_Elem "Nil") ["a"] [T_TRep (T_Hole "a")];
  C_DeclCombVariant "List" (T_Elem "Cons") ["a"] [T_Hole "a"; T_Comb "List" [T_Hole "a"]];
  C_CloseCombType "List";
  C_DeclVar "zero" (E_Comb (E_Elem "Zero") []);
  C_Eval (E_Comb (E_Elem "Cons") [
      E_Var "zero"; 
      (E_Comb (E_Elem "Nil") [E_TRep (T_Comb "Nat" [])])
  ])
].
Compute (run_prog example_good_prog7).

(* Плохая программа - несоблюдение ограничений типов *)
Example example_bad_prog0 := [
  C_DeclCombVariant "Foo" (T_Elem "Foo") [] [T_Hole "a"; T_Hole "a"];
  C_CloseCombType "Foo";
  C_Eval (E_Comb (E_Elem "Foo") [E_Unit; E_Elem "bla"])
].
Compute (run_prog example_bad_prog0).

(* Плохая программа - undefined variable bad *)
Example example_bad_prog1 := [
  C_DeclVar "bed" (E_Elem "()"); 
  C_Eval (E_Var "bad")].
Compute (run_prog example_bad_prog1).

(* Плохая программа - затенение переменных *)
Example example_bad_prog2 := [
  C_DeclVar "input" (E_Elem "bla");
  C_DeclVar "input" (E_Prod [E_Elem "0"; E_Elem "2"; E_Elem "VAL"])
].
Compute (run_prog example_bad_prog2).

(* Плохая программа - объявление типов и их синонимов с занятыми именами *)
Example example_bad_prog3 : prog := [
  C_NewTypeAbbr "NatZero" (T_Elem "Nat");
  C_DeclCombVariant "NatZero" (T_Prod [T_Elem "Zero"; (T_Prod [T_Elem "Nat"])]) [] []
].
Compute (run_prog example_bad_prog3).

(* Плохая программа - объявление типов комбинаций с одинаковым конструктором данных *)
Example example_bad_prog4 : prog := [
  C_NewTypeAbbr "TP" (T_Prod [T_Elem "Zero"; T_Elem "Nat"]);
  C_DeclCombVariant "NatZero" (T_Prod [T_Elem "Zero"; T_Elem "Nat"]) [] [];
  C_DeclCombVariant "NatZeroCopy" (T_Abbr "TP") [] []
].
Compute (run_prog example_bad_prog4).

(* Плохая программа - попытка расширить закрытый тип *)
Example example_bad_prog5 : prog := [
  C_DeclCombVariant "Bool" (T_Elem "true") [] [];
  C_DeclCombVariant "Bool" (T_Elem "false") [] [];
  C_CloseCombType "Bool";
  C_DeclCombVariant "Bool" (T_Elem "undef") [] [];
  C_Eval (E_Comb (E_Elem "false") [])
].
Compute (run_prog example_bad_prog5).

(* Плохая программа - попытка использовать T_Prim в конструкторе данных для типа комбинации 
   в объявлении типа комбинации *)
Example example_bad_prog6 : prog := [
  C_DeclCombVariant "Bar" (T_Prod [T_Elem "a"; T_Prim Prm_Left]) [] []
].
Compute (run_prog example_bad_prog6).

(* Плохая программа - попытка использовать T_Prim в параметрах типа комбинации 
   в объявлении типа комбинации *)
Example example_bad_prog7 : prog := [
  C_DeclCombVariant "Bar" (T_Elem "a") [] [T_Prod [T_Prim Prm_Left; T_Elem "x"]]
].
Compute (run_prog example_bad_prog7).

(* Плохая программа - ошибочное применение Prm_Left *)
Example example_good_prog8 := [
  C_DeclVar "myvar" (E_Prod []);
  C_Eval (E_App (E_Var "myvar") (E_Prim Prm_Left))].
Compute (run_prog example_good_prog8).

(* Плохая программа - закрытие несуществующего типа *)
Example example_good_prog9 := [
  C_CloseCombType "Bool"
].
Compute (run_prog example_good_prog9).

(* Плохая программа - повторное закрытие типа *)
Example example_good_prog10 := [
  C_DeclCombVariant "Bool" (T_Elem "true") [] [];
  C_DeclCombVariant "Bool" (T_Elem "false") [] [];
  C_CloseCombType "Bool";
  C_CloseCombType "Bool"
].
Compute (run_prog example_good_prog10).

Example norm_type_self_reference_fuel_exhausted :
  norm_type
    [BindTypeAbbr "A" (T_Abbr "A")]
    (T_Abbr "A")
  =
  Err TypeErr_InvalidType.
Proof.
  reflexivity.
Qed.

Example norm_type_indirect_cycle_fuel_exhausted :
  norm_type
    [BindTypeAbbr "A" (T_Abbr "B");
     BindTypeAbbr "B" (T_Abbr "A")]
    (T_Abbr "A")
  =
  Err TypeErr_InvalidType.
Proof.
  reflexivity.
Qed.

Example norm_type_large_indirect_cycle_fuel_exhausted :
  norm_type
    [BindTypeAbbr "A" (T_Abbr "B");
     BindTypeAbbr "B" (T_Abbr "C");
     BindTypeAbbr "C" (T_Abbr "D");
     BindTypeAbbr "D" (T_Abbr "E");
     BindTypeAbbr "E" (T_Abbr "A")]
    (T_Abbr "A")
  =
  Err TypeErr_InvalidType.
Proof.
  reflexivity.
Qed.

Example self_abbr_is_unbound :
  unfold_prog
    [C_NewTypeAbbr "A" (T_Abbr "A")]
  =
    Err (Err_UnboundTypeAbbr "A").
Proof.
  reflexivity.
Qed.

Example forward_abbr_is_unbound :
  unfold_prog
    [C_NewTypeAbbr "A" (T_Abbr "B"); C_NewTypeAbbr "B" (T_Abbr "A")]
  =
    Err (Err_UnboundTypeAbbr "B").
Proof.
  reflexivity.
Qed.

Example unify_map_empty :
  unify_type []
    (T_Map [])
    (T_Map []) =
  Ok [].
Proof.
  reflexivity.
Qed.

Example unify_empty_map_pattern :
  unify_type []
    (T_Map [])
    (T_Map
       [(T_Elem "key1", T_Elem "value1");
        (T_Elem "key2", T_Elem "value2")]) =
  Ok [].
Proof.
  reflexivity.
Qed.

Example valid_map_pattern_ok :
  validate_map_pattern_keys
    (T_Map
       [(T_Elem "key1", T_Hole "V1");
        (T_Elem "key2", T_Hole "V2")]) =
  Ok tt.
Proof.
  reflexivity.
Qed.

Example invalid_duplicate_map_pattern_key :
  validate_map_pattern_keys
    (T_Map
       [(T_Elem "key", T_Hole "V1");
        (T_Elem "key", T_Hole "V2")]) =
  Err
    (TypeErr_DuplicateMapPatternKey
       (T_Elem "key")).
Proof.
  reflexivity.
Qed.

Example invalid_hole_in_map_pattern_key :
  validate_map_pattern_keys
    (T_Map
       [(T_Hole "K", T_Hole "V")]) =
  Err
    (TypeErr_HoleInMapPatternKey
       (T_Hole "K")).
Proof.
  reflexivity.
Qed.

Example invalid_nested_duplicate_map_pattern_key :
  validate_map_pattern_keys
    (T_Map
       [(T_Elem "outer",
         T_Map
           [(T_Elem "inner", T_Hole "V1");
            (T_Elem "inner", T_Hole "V2")])]) =
  Err
    (TypeErr_DuplicateMapPatternKey
       (T_Elem "inner")).
Proof.
  reflexivity.
Qed.

Example duplicate_after_norm_context : type_context :=
  [BindTypeAbbr "AliasKey" (T_Elem "key")].

Example duplicate_map_key_after_normalization :
  match
    norm_type
      duplicate_after_norm_context
      (T_Map
         [(T_Abbr "AliasKey", T_Hole "V1");
          (T_Elem "key", T_Hole "V2")])
  with
  | Err e =>
      Err e
  | Ok T =>
      validate_map_pattern_keys T
  end =
  Err
    (TypeErr_DuplicateMapPatternKey
       (T_Elem "key")).
Proof.
  reflexivity.
Qed.

Example unify_map_rejects_hole_in_key :
  unify_type []
    (T_Map
       [(T_Hole "K", T_Hole "V")])
    (T_Map
       [(T_Elem "key", T_Elem "value");
        (T_Elem "key2", T_Elem "val")]) =
  Err
    (TypeErr_HoleInMapPatternKey
       (T_Hole "K")).
Proof.
  reflexivity.
Qed.

Example unify_map_rejects_nested_hole_in_key :
  unify_type []
    (T_Map
       [(T_Prod
           [T_Elem "prefix";
            T_Hole "K"],
         T_Hole "V")])
    (T_Map
       [(T_Prod
           [T_Elem "prefix";
            T_Elem "key"],
         T_Elem "value")]) =
  Err
    (TypeErr_HoleInMapPatternKey
       (T_Prod
          [T_Elem "prefix";
           T_Hole "K"])).
Proof.
  reflexivity.
Qed.


Example unify_map_permuted :
  unify_type []
    (T_Map
       [(T_Elem "key1", T_Hole "V1");
        (T_Elem "key2", T_Hole "V2")])
    (T_Map
       [(T_Elem "key2", T_Prim Prm_Right);
        (T_Elem "key3", T_Elem "unused");
        (T_Elem "key1", T_Prim Prm_Left)]) =
  Ok
    [("V2", T_Prim Prm_Right);
     ("V1", T_Prim Prm_Left)].
Proof.
  reflexivity.
Qed.

Example unify_map_concrete_key :
  unify_type []
    (T_Map
       [(T_Elem "key", T_Hole "V")])
    (T_Map
       [(T_Elem "key", T_Elem "value");
        (T_Elem "key2", T_Elem "val")]) =
  Ok
    [("V", T_Elem "value")].
Proof.
  reflexivity.
Qed.

Example unify_map_shared_value_hole :
  unify_type []
    (T_Map
       [(T_Elem "key1", T_Hole "V");
        (T_Elem "key2", T_Hole "V")])
    (T_Map
       [(T_Elem "key2", T_Prim Prm_Left);
        (T_Elem "key1", T_Prim Prm_Left)]) =
  Ok
    [("V", T_Prim Prm_Left)].
Proof.
  reflexivity.
Qed.

Example unify_map_different_lengths :
  unify_type []
    (T_Map
       [(T_Elem "a", T_Hole "X")])
    (T_Map
       [(T_Elem "a", T_Prim Prm_Left);
        (T_Elem "b", T_Prim Prm_Right)]) =
  Ok [("X", T_Prim Prm_Left)].
Proof.
  reflexivity.
Qed.

Example unify_map_inconsistent_value_hole :
  unify_type []
    (T_Map
       [(T_Elem "key1", T_Hole "V");
        (T_Elem "key2", T_Hole "V")])
    (T_Map
       [(T_Elem "key1", T_Prim Prm_Left);
        (T_Elem "key2", T_Prim Prm_Right)]) =
  Err
    (TypeErr_Mismatch
       (T_Prim Prm_Left)
       (T_Prim Prm_Right)).
Proof.
  reflexivity.
Qed.

Example unify_map_missing_key :
  unify_type []
    (T_Map
       [(T_Elem "missing", T_Hole "V")])
    (T_Map
       [(T_Elem "key", T_Elem "value")]) =
  Err
    (TypeErr_Mismatch
       (T_Map
          [(T_Elem "missing", T_Hole "V")])
       (T_Map
          [(T_Elem "key", T_Elem "value")])).
Proof.
  reflexivity.
Qed.

Example type_beq_map_permutation :
  type_beq
    (T_Map
       [(T_Elem "K1", T_Elem "V1");
        (T_Elem "K2", T_Elem "V2")])
    (T_Map
       [(T_Elem "K2", T_Elem "V2");
        (T_Elem "K1", T_Elem "V1")])
  = true.
Proof.
  reflexivity.
Qed.

Example type_beq_map_different_values :
  type_beq
    (T_Map
       [(T_Elem "K1", T_Elem "V1");
        (T_Elem "K2", T_Elem "V2")])
    (T_Map
       [(T_Elem "K2", T_Elem "X");
        (T_Elem "K1", T_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example type_beq_map_different_lengths :
  type_beq
    (T_Map
       [(T_Elem "K1", T_Elem "V1")])
    (T_Map
       [(T_Elem "K1", T_Elem "V1");
        (T_Elem "K2", T_Elem "V2")])
  = false.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_permutation :
  expr_beq
    (E_Map
       [(E_Elem "K1", E_Elem "V1");
        (E_Elem "K2", E_Elem "V2")])
    (E_Map
       [(E_Elem "K2", E_Elem "V2");
        (E_Elem "K1", E_Elem "V1")])
  = true.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_same_keys_different_values :
  expr_beq
    (E_Map
       [(E_Elem "K1", E_Elem "V1");
        (E_Elem "K2", E_Elem "V2")])
    (E_Map
       [(E_Elem "K2", E_Elem "X");
        (E_Elem "K1", E_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_different_keys :
  expr_beq
    (E_Map
       [(E_Elem "K1", E_Elem "V1");
        (E_Elem "K2", E_Elem "V2")])
    (E_Map
       [(E_Elem "K3", E_Elem "V2");
        (E_Elem "K1", E_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_different_lengths :
  expr_beq
    (E_Map
       [(E_Elem "K1", E_Elem "V1")])
    (E_Map
       [(E_Elem "K1", E_Elem "V1");
        (E_Elem "K2", E_Elem "V2")])
  = false.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_nested_permutation :
  expr_beq
    (E_Map
       [(E_Elem "outer",
         E_Map
           [(E_Elem "K1", E_Elem "V1");
            (E_Elem "K2", E_Elem "V2")])])
    (E_Map
       [(E_Elem "outer",
         E_Map
           [(E_Elem "K2", E_Elem "V2");
            (E_Elem "K1", E_Elem "V1")])])
  = true.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_entry_permutation_and_nested_permutation :
  expr_beq
    (E_Map
       [(E_Elem "A",
         E_Map
           [(E_Elem "K1", E_Elem "V1");
            (E_Elem "K2", E_Elem "V2")]);
        (E_Elem "B", E_Elem "VB")])
    (E_Map
       [(E_Elem "B", E_Elem "VB");
        (E_Elem "A",
         E_Map
           [(E_Elem "K2", E_Elem "V2");
            (E_Elem "K1", E_Elem "V1")])])
  = true.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_duplicate_multiplicity_equal :
  expr_beq
    (E_Map
       [(E_Elem "K", E_Elem "V");
        (E_Elem "K", E_Elem "V");
        (E_Elem "X", E_Elem "Y")])
    (E_Map
       [(E_Elem "X", E_Elem "Y");
        (E_Elem "K", E_Elem "V");
        (E_Elem "K", E_Elem "V")])
  = true.
Proof.
  reflexivity.
Qed.

Example expr_beq_map_duplicate_multiplicity_different :
  expr_beq
    (E_Map
       [(E_Elem "K", E_Elem "V");
        (E_Elem "K", E_Elem "V")])
    (E_Map
       [(E_Elem "K", E_Elem "V");
        (E_Elem "X", E_Elem "Y")])
  = false.
Proof.
  reflexivity.
Qed.


Example value_beq_map_permutation :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
    (V_Map
       [(V_Elem "K2", V_Elem "V2");
        (V_Elem "K1", V_Elem "V1")])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_same_keys_different_values :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
    (V_Map
       [(V_Elem "K2", V_Elem "X");
        (V_Elem "K1", V_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_map_different_keys :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
    (V_Map
       [(V_Elem "K3", V_Elem "V2");
        (V_Elem "K1", V_Elem "V1")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_map_different_lengths :
  value_beq
    (V_Map
       [(V_Elem "K1", V_Elem "V1")])
    (V_Map
       [(V_Elem "K1", V_Elem "V1");
        (V_Elem "K2", V_Elem "V2")])
  = false.
Proof.
  reflexivity.
Qed.

Example value_beq_map_nested_permutation :
  value_beq
    (V_Map
       [(V_Elem "outer",
         V_Map
           [(V_Elem "K1", V_Elem "V1");
            (V_Elem "K2", V_Elem "V2")])])
    (V_Map
       [(V_Elem "outer",
         V_Map
           [(V_Elem "K2", V_Elem "V2");
            (V_Elem "K1", V_Elem "V1")])])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_entry_permutation_and_nested_permutation :
  value_beq
    (V_Map
       [(V_Elem "A",
         V_Map
           [(V_Elem "K1", V_Elem "V1");
            (V_Elem "K2", V_Elem "V2")]);
        (V_Elem "B", V_Elem "VB")])
    (V_Map
       [(V_Elem "B", V_Elem "VB");
        (V_Elem "A",
         V_Map
           [(V_Elem "K2", V_Elem "V2");
            (V_Elem "K1", V_Elem "V1")])])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_duplicate_multiplicity_equal :
  value_beq
    (V_Map
       [(V_Elem "K", V_Elem "V");
        (V_Elem "K", V_Elem "V");
        (V_Elem "X", V_Elem "Y")])
    (V_Map
       [(V_Elem "X", V_Elem "Y");
        (V_Elem "K", V_Elem "V");
        (V_Elem "K", V_Elem "V")])
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_map_duplicate_multiplicity_different :
  value_beq
    (V_Map
       [(V_Elem "K", V_Elem "V");
        (V_Elem "K", V_Elem "V")])
    (V_Map
       [(V_Elem "K", V_Elem "V");
        (V_Elem "X", V_Elem "Y")])
  = false.
Proof.
  reflexivity.
Qed.


Example expr_beq_trep_map_permutation :
  expr_beq
    (E_TRep
       (T_Map
          [(T_Elem "K1", T_Elem "V1");
           (T_Elem "K2", T_Elem "V2")]))
    (E_TRep
       (T_Map
          [(T_Elem "K2", T_Elem "V2");
           (T_Elem "K1", T_Elem "V1")]))
  = true.
Proof.
  reflexivity.
Qed.

Example value_beq_trep_map_permutation :
  value_beq
    (V_TRep
       (T_Map
          [(T_Elem "K1", T_Elem "V1");
           (T_Elem "K2", T_Elem "V2")]))
    (V_TRep
       (T_Map
          [(T_Elem "K2", T_Elem "V2");
           (T_Elem "K1", T_Elem "V1")]))
  = true.
Proof.
  reflexivity.
Qed.


Example infer_map_duplicate_key_test :
  infer_type_expr
    []
    (E_Map
       [(E_Elem "a", E_Elem "1");
        (E_Elem "a", E_Elem "2")])
  =
  Err (TypeErr_DuplicateMapKey (T_Elem "a")).
Proof.
  reflexivity.
Qed.

Example eval_map_duplicate_key_test :
  eval_expr
    (E_Map
       [(E_Elem "a", E_Elem "1");
        (E_Elem "a", E_Elem "2")])
  =
  Err (ExprErr_DuplicateMapKey (E_Elem "a")).
Proof.
  reflexivity.
Qed.

Example map_expr : expr :=
  E_Map
    [(E_Elem "a", E_Elem "1");
     (E_Elem "b", E_Prod [E_Elem "x"; E_Elem "y"])].

Example infer_map_expr_test :
  infer_type_expr [] map_expr =
  Ok
    (T_Map
       [(T_Elem "a", T_Elem "1");
        (T_Elem "b",
         T_Prod [T_Elem "x"; T_Elem "y"])]).
Proof.
  reflexivity.
Qed.

Example eval_map_expr_test :
  eval_expr map_expr =
  Ok
    (V_Map
       [(V_Elem "a", V_Elem "1");
        (V_Elem "b",
         V_Prod [V_Elem "x"; V_Elem "y"])]).
Proof.
  reflexivity.
Qed.


Definition map_type_context : type_context :=
  [BindTypeAbbr "A" (T_Elem "a");
   BindTypeAbbr "B" (T_Elem "b")].

Example norm_map_type_test :
  norm_type
    map_type_context
    (T_Map
       [(T_Abbr "A", T_Abbr "B")])
  =
  Ok
    (T_Map
       [(T_Elem "a", T_Elem "b")]).
Proof.
  reflexivity.
Qed.


Example test_unify_nested_prod :
  unify_generic_list
    [T_Prod [
       T_Hole "a";
       T_Elem "x"
    ]]
    [T_Prod [
       T_Elem "Nat";
       T_Elem "x"
    ]]
  =
  Ok [
    T_Prod [
      T_Elem "Nat";
      T_Elem "x"
    ]
  ].
Proof.
  reflexivity.
Qed.


Example test_unify_repeated_nested_hole :
  unify_generic_list
    [
      T_Hole "a";
      T_Comb "Option" [T_Hole "a"]
    ]
    [
      T_Elem "Nat";
      T_Comb "Option" [T_Elem "Nat"]
    ]
  =
  Ok [
    T_Elem "Nat";
    T_Comb "Option" [T_Elem "Nat"]
  ].
Proof.
  reflexivity.
Qed.

Example test_unify_repeated_nested_hole_error :
  unify_generic_list
    [
      T_Hole "a";
      T_Comb "Option" [T_Hole "a"]
    ]
    [
      T_Elem "Nat";
      T_Comb "Option" [T_Elem "Bool"]
    ]
  =
  Err
    (TypeErr_Mismatch
       (T_Elem "Nat")
       (T_Elem "Bool")).
Proof.
  reflexivity.
Qed.

Example test_unify_different_comb_names :
  unify_generic_list
    [T_Comb "Option" [T_Hole "a"]]
    [T_Comb "List" [T_Elem "Nat"]]
  =
  Err
    (TypeErr_Mismatch
       (T_Comb "Option" [T_Hole "a"])
       (T_Comb "List" [T_Elem "Nat"])).
Proof.
  reflexivity.
Qed.

Example test_unify_product_length_error :
  unify_generic_list
    [
      T_Prod [
        T_Hole "a";
        T_Hole "b";
        T_Hole "c"
      ]
    ]
    [
      T_Prod [
        T_Elem "Nat";
        T_Elem "Nat2"
      ]
    ]
  =
  Err
    (TypeErr_ListMismatch
       [T_Hole "a"; T_Hole "b"; T_Hole "c"]
       [T_Elem "Nat"; T_Elem "Nat2"]).
Proof.
  reflexivity.
Qed.

