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

Inductive core_type : Type :=
  | CT_Hole : string -> core_type
  | CT_Elem : elem -> core_type
  | CT_Prim : prim -> core_type
  | CT_TRep : core_type -> core_type
  | CT_Prod : list core_type -> core_type
  | CT_Comb : TypeName -> list core_type -> core_type
  | CT_Map : list (core_type * core_type) -> core_type.

Inductive norm_type : Type :=
  | NT_Hole : string -> norm_type
  | NT_Elem : elem -> norm_type
  | NT_Prim : prim -> norm_type
  | NT_TRep : norm_type -> norm_type
  | NT_Unit : norm_type
  | NT_Prod :
      norm_type ->
      norm_type ->
      list norm_type ->
      norm_type
  | NT_Comb :
      TypeName ->
      list norm_type ->
      norm_type
  | NT_Map :
      list (norm_type * norm_type) ->
      norm_type.

Inductive core_expr : Type :=
  | CE_Elem : elem -> core_expr
  | CE_Prim : prim -> core_expr
  | CE_TRep : core_type -> core_expr
  | CE_Prod : list core_expr -> core_expr
  | CE_Comb : core_expr -> list core_expr -> core_expr
  | CE_Map : list (core_expr * core_expr) -> core_expr
  | CE_App : core_expr -> core_expr -> core_expr.

Inductive value : Type :=
  | V_Elem : elem -> value
  | V_Prim : prim -> value
  | V_TRep : norm_type -> value
  | V_Prod : list value -> value
  | V_Comb : value -> list value -> value
  | V_Map : list (value * value) -> value.

Inductive core_command : Type :=
  | CC_DeclCombVariant :
      TypeName ->
      core_type ->
      list string ->
      list core_type ->
      core_command
  | CC_CloseCombType :
      TypeName ->
      core_command
  | CC_Eval :
      core_expr ->
      core_command.

Definition core_prog : Type :=
  list core_command.

Inductive source_type : Type :=
  | ST_Hole : string -> source_type
  | ST_Abbr : TypeName -> source_type
  | ST_Elem : elem -> source_type
  | ST_Prim : prim -> source_type
  | ST_TRep : source_type -> source_type
  | ST_Prod : list source_type -> source_type
  | ST_Comb : TypeName -> list source_type -> source_type
  | ST_Map : list (source_type * source_type) -> source_type.

Inductive source_expr : Type :=
  | SE_Var : VarName -> source_expr
  | SE_Elem : elem -> source_expr
  | SE_Prim : prim -> source_expr
  | SE_TRep : source_type -> source_expr
  | SE_Prod : list source_expr -> source_expr
  | SE_Comb :
      source_expr ->
      list source_expr ->
      source_expr
  | SE_Map :
      list (source_expr * source_expr) ->
      source_expr
  | SE_App :
      source_expr ->
      source_expr ->
      source_expr.

Inductive source_command : Type :=
  | SC_DeclVar :
      VarName ->
      source_expr ->
      source_command
  | SC_NewTypeAbbr :
      TypeName ->
      source_type ->
      source_command
  | SC_DeclCombVariant :
      TypeName ->
      source_type ->
      list string ->
      list source_type ->
      source_command
  | SC_CloseCombType :
      TypeName ->
      source_command
  | SC_Eval :
      source_expr ->
      source_command.

Definition source_prog : Type :=
  list source_command.

Inductive error : Type :=
  | InternalErr_UnificationFuelExhausted : error
  | Err_UnboundVar : VarName -> error
  | Err_UnboundTypeAbbr : TypeName -> error
  | Err_UnboundHole : string -> error
  | Err_DuplicateVar : VarName -> error
  | TypeErr_UseHole : norm_type -> error
  | TypeErr_DeclaredHoleNotUsed : string -> error
  | TypeErr_UndeclaredHole : string -> error
  | TypeErr_DuplicateHoleName : string -> error
  | TypeErr_InvalidApp : norm_type -> norm_type -> error
  | TypeErr_DuplicateType : TypeName -> error
  | TypeErr_DuplicateCombSignature : TypeName -> norm_type -> error
  | TypeErr_DuplicateMapKey : norm_type -> error
  | TypeErr_DuplicateMapPatternKey : norm_type -> error
  | TypeErr_HoleInMapPatternKey : norm_type -> error
  | TypeErr_UnknownCombSignature : error
  | TypeErr_UnknownCombType : TypeName -> error
  | TypeErr_ExpectedCombType : TypeName -> error
  | TypeErr_InvalidProd : core_type -> error
  | TypeErr_Mismatch : norm_type -> norm_type -> error
  | TypeErr_CombClosed : TypeName -> error
  | TypeErr_CloseUnknownComb : TypeName -> error
  | TypeErr_CombAlreadyClosed : TypeName -> error
  | TypeErr_ListMismatch : list norm_type -> list norm_type -> error
  | TypeErr_UsePrimInDeclCombCtor : norm_type -> error
  | TypeErr_UsePrimInDeclCombParam : list norm_type -> error
  | ExprErr_DuplicateMapKey : core_expr -> error
  | ExprErr_InvalidProd : core_expr -> error
  | ExprErr_UseHole : core_expr -> error
  | ExprErr_InvalidApp : core_expr -> core_expr -> error.

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
  | BindCombType : TypeName -> norm_type -> list string -> list norm_type -> TypeBinding
  | CloseCombType : TypeName -> TypeBinding.

Definition type_context : Type := list TypeBinding.

Fixpoint erase_norm_type
    (T : norm_type)
  : core_type :=
  let fix erase_norm_type_pair (p : (norm_type * norm_type))
    : (core_type * core_type) := (erase_norm_type (fst p), erase_norm_type (snd p))
  in
  match T with
  | NT_Hole X => CT_Hole X
  | NT_Elem e => CT_Elem e
  | NT_Prim p => CT_Prim p
  | NT_TRep T1 => CT_TRep (erase_norm_type T1)
  | NT_Unit => CT_Prod []
  | NT_Prod T1 T2 rest => CT_Prod (map erase_norm_type (T1 :: T2 :: rest))
  | NT_Comb tn Ts => CT_Comb tn (map erase_norm_type Ts)
  | NT_Map entries => CT_Map (map erase_norm_type_pair entries)
  end.

Fixpoint normalize_core_type_list_aux
    (f : core_type -> result norm_type)
    (types : list core_type)
  : result (list norm_type) :=
  match types with
  | [] =>
      Ok []
  | T :: rest =>
      T' <- f T ;;
      rest' <- normalize_core_type_list_aux f rest ;;
      Ok (T' :: rest')
  end.

Fixpoint normalize_core_type
    (T : core_type)
  : result norm_type :=
  let fix normalize_map_entries
      (entries : list (core_type * core_type))
      {struct entries}
    : result
        (list (norm_type * norm_type)) :=
    match entries with
    | [] => Ok []
    | (K, V) :: rest =>
        K' <- normalize_core_type K ;;
        V' <- normalize_core_type V ;;
        rest' <- normalize_map_entries rest ;;
        Ok ((K', V') :: rest')
    end
  in
  match T with
  | CT_Hole X => Ok (NT_Hole X)
  | CT_Elem e => Ok (NT_Elem e)
  | CT_Prim p => Ok (NT_Prim p)
  | CT_TRep T1 =>
      T1N <- normalize_core_type T1 ;;
      Ok (NT_TRep T1N)
  | CT_Prod Ts =>
      TsN <- normalize_core_type_list Ts ;;
      match TsN with
      | [] => Ok NT_Unit
      | [T1] => Err (TypeErr_InvalidProd T)
      | T1 :: T2 :: rest => Ok (NT_Prod T1 T2 rest)
      end
  | CT_Comb tn Ts =>
      TsN <- normalize_core_type_list Ts ;;
      Ok (NT_Comb tn TsN)
  | CT_Map entries =>
      entriesN <- normalize_map_entries entries ;;
      Ok (NT_Map entriesN)
  end
with normalize_core_type_list 
    (types : list core_type)
    : result (list norm_type) :=
    normalize_core_type_list_aux normalize_core_type types.

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

Fixpoint norm_type_beq
    (T1 T2 : norm_type)
  : bool :=
  match T1, T2 with
  | NT_Hole X, NT_Hole Y => eqb X Y
  | NT_Elem e1, NT_Elem e2 => eqb e1 e2
  | NT_Prim p1, NT_Prim p2 => prim_beq p1 p2
  | NT_TRep T1', NT_TRep T2' => norm_type_beq T1' T2'
  | NT_Unit, NT_Unit => true
  | NT_Prod T11 T12 Ts1, NT_Prod T21 T22 Ts2 =>
      norm_type_beq T11 T21 &&
      norm_type_beq T12 T22 &&
      list_eqb norm_type_beq Ts1 Ts2
  | NT_Comb X Ts1, NT_Comb Y Ts2 =>
      eqb X Y && list_eqb norm_type_beq Ts1 Ts2
  | NT_Map entries1, NT_Map entries2 =>
      permutation_eqb
        (pair_eqb
          norm_type_beq
          norm_type_beq)
        entries1
        entries2

  | _, _ =>
      false
  end.
 
Definition norm_type_mem
    (T : norm_type)
    (Ts : list norm_type)
  : bool :=
  existsb (norm_type_beq T) Ts.

Fixpoint norm_type_contains_hole
    (T : norm_type)
  : bool :=
  match T with
  | NT_Hole _ => true
  | NT_Elem _ => false
  | NT_Prim _ => false
  | NT_Unit => false
  | NT_TRep T1 =>
      norm_type_contains_hole T1
  | NT_Prod T1 T2 rest => existsb norm_type_contains_hole (T1 :: T2 :: rest)
  | NT_Comb _ args => existsb norm_type_contains_hole args
  | NT_Map entries =>
      existsb
        (fun entry =>
           let '(K, V) := entry in
           norm_type_contains_hole K || norm_type_contains_hole V)
        entries
  end.

Fixpoint norm_type_contains_prim (T : norm_type) : bool :=
  match T with
  | NT_Prim _ => true
  | NT_Hole _ => false
  | NT_Elem _ => false
  | NT_Unit => false
  | NT_TRep T1 => norm_type_contains_prim T1
  | NT_Prod T1 T2 rest => existsb norm_type_contains_prim (T1 :: T2 :: rest)
  | NT_Comb _ Ts => existsb norm_type_contains_prim Ts
  | NT_Map entries =>
      existsb
        (fun entry =>
           let '(K, V) := entry in
           norm_type_contains_prim K || norm_type_contains_prim V)
        entries
  end.

Fixpoint norm_type_size
    (T : norm_type)
  : nat :=
  let fix type_list_size
      (Ts : list norm_type)
    : nat :=
    match Ts with
    | [] => 0
    | T1 :: rest =>
        norm_type_size T1 +
        type_list_size rest
    end
  in
  let fix map_entries_size
      (entries : list (norm_type * norm_type))
    : nat :=
    match entries with
    | [] => 0
    | (K, V) :: rest =>
        norm_type_size K +
        norm_type_size V +
        map_entries_size rest
    end
  in
  match T with
  | NT_Hole _ => 1
  | NT_Elem _ => 1
  | NT_Prim _ => 1
  | NT_TRep T1 => S (norm_type_size T1)
  | NT_Unit => 1
  | NT_Prod T1 T2 rest =>
      S
        (norm_type_size T1 +
         norm_type_size T2 +
         type_list_size rest)
  | NT_Comb _ args => S (type_list_size args)
  | NT_Map entries => S (map_entries_size entries)
  end.

Fixpoint find_duplicate_map_key
    (seen_keys : list norm_type)
    (entries : list (norm_type * norm_type))
  : option norm_type :=
  match entries with
  | [] => None
  | (key, _) :: rest =>
      if norm_type_mem key seen_keys then
        Some key
      else
        find_duplicate_map_key
          (key :: seen_keys)
          rest
  end.

Fixpoint validate_map_pattern_keys
    (T : norm_type)
  : result unit :=
  let fix validate_entries
      (seen_keys : list norm_type)
      (entries : list (norm_type * norm_type))
    : result unit :=
    match entries with
    | [] => Ok tt
    | (key, value) :: rest =>
        if norm_type_contains_hole key then
          Err
            (TypeErr_HoleInMapPatternKey key)
        else if
          norm_type_mem key seen_keys
        then
          Err
            (TypeErr_DuplicateMapPatternKey key)
        else
          _ <- validate_map_pattern_keys key ;;
          _ <- validate_map_pattern_keys value ;;
          validate_entries
            (key :: seen_keys)
            rest
    end
  in
  match T with
  | NT_Hole _ => Ok tt
  | NT_Elem _ => Ok tt
  | NT_Prim _ => Ok tt
  | NT_TRep T1 => validate_map_pattern_keys T1
  | NT_Unit => Ok tt
  | NT_Prod T1 T2 rest =>
      _ <- validate_map_pattern_keys T1 ;;
      _ <- validate_map_pattern_keys T2 ;;
      validate_list validate_map_pattern_keys rest
  | NT_Comb _ args => validate_list validate_map_pattern_keys args
  | NT_Map entries => validate_entries [] entries
  end.

Definition type_subst : Type := list (string * norm_type).

Fixpoint type_hole_lookup (subst : type_subst) (X : string) : option norm_type :=
  match subst with
  | [] => None
  | (Y, T) :: rest =>
      if eqb X Y then Some T else type_hole_lookup rest X
  end.

Fixpoint apply_type_subst
    (subst : type_subst)
    (T : norm_type)
  : norm_type :=
  let fix apply_type_subst_list
      (Ts : list norm_type)
    : list norm_type :=
    match Ts with
    | [] => []
    | T1 :: rest =>
        apply_type_subst subst T1 ::
        apply_type_subst_list rest
    end
  in
  let fix apply_type_subst_entries
      (entries : list (norm_type * norm_type))
    : list (norm_type * norm_type) :=
    match entries with
    | [] => []
    | (K, V) :: rest =>
        (apply_type_subst subst K,
         apply_type_subst subst V) ::
        apply_type_subst_entries rest
    end
  in
  match T with
  | NT_Hole X =>
      match type_hole_lookup subst X with
      | Some T' => T'
      | None => NT_Hole X
      end
  | NT_Elem e => NT_Elem e
  | NT_Prim p => NT_Prim p
  | NT_TRep T1 => NT_TRep (apply_type_subst subst T1)
  | NT_Unit => NT_Unit
  | NT_Prod T1 T2 rest =>
      NT_Prod
        (apply_type_subst subst T1)
        (apply_type_subst subst T2)
        (apply_type_subst_list rest)
  | NT_Comb tn args =>
      NT_Comb tn (apply_type_subst_list args)
  | NT_Map entries =>
      NT_Map (apply_type_subst_entries entries)
  end.

Fixpoint eval_core_expr_list (f : core_expr -> result value) (ts : list core_expr)
  : result (list value) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      v <- f t ;;
      vs <- eval_core_expr_list f rest ;;
      Ok (v :: vs)
  end.

Record machine_state : Type := {
  ms_type_ctx : type_context;
  ms_last_type : norm_type;
  ms_last_value : value
}.

Notation CT_Unit := (CT_Prod []).
Notation SE_Unit := (SE_Prod []).
Notation V_Unit := (V_Prod []).

Definition initial_state : machine_state :=
  {| ms_type_ctx := [];
     ms_last_type := NT_Unit;
     ms_last_value := V_Prod [] |}.

Fixpoint normal_type_comb_lookup
    (Gamma : type_context)
    (ctor : norm_type)
    {struct Gamma}
  : option (TypeName * norm_type * list string * list norm_type) :=
  match Gamma with
  | [] => None
  | BindCombType TN defctor holenames defargs :: rest =>
      if norm_type_beq ctor defctor then
        Some (TN, defctor, holenames, defargs)
      else
        normal_type_comb_lookup rest ctor
  | _ :: rest => normal_type_comb_lookup rest ctor
  end.

Fixpoint infer_list
    {A : Type}
    (f : type_context -> A -> result norm_type)
    (Gamma : type_context)
    (ts : list A)
    {struct ts}
  : result (list norm_type) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      T <- f Gamma t ;;
      Ts <- infer_list f Gamma rest ;;
      Ok (T :: Ts)
  end.

Fixpoint comb_type_closed (Gamma : type_context) (TN : TypeName) : bool :=
  match Gamma with
  | [] => false
  | CloseCombType TN' :: rest =>
      if eqb TN TN' then true else comb_type_closed rest TN
  | _ :: rest => comb_type_closed rest TN
  end.

Fixpoint comb_type_declared (Gamma : type_context) (TN : TypeName) : bool :=
  match Gamma with
  | [] => false
  | BindCombType TN' _ _ _ :: rest =>
      if eqb TN TN' then true else comb_type_declared rest TN
  | _ :: rest => comb_type_declared rest TN
  end.

Fixpoint value_beq (v1 v2 : value) : bool :=
  match v1, v2 with
  | V_Elem e1, V_Elem e2 => eqb e1 e2
  | V_Prim p1, V_Prim p2 => prim_beq p1 p2
  | V_TRep T1, V_TRep T2 => norm_type_beq T1 T2
  | V_Prod vs1, V_Prod vs2 => list_eqb value_beq vs1 vs2
  | V_Comb ctor1 args1, V_Comb ctor2 args2 =>
      value_beq ctor1 ctor2 && list_eqb value_beq args1 args2
  | V_Map lst1, V_Map lst2 =>
      permutation_eqb (pair_eqb value_beq value_beq) lst1 lst2
  | _, _ =>
      false
  end.

Fixpoint unify_norm_type_fuel
    (fuel : nat)
    (subst : type_subst)
    (ptrn actual : norm_type)
  : result type_subst :=
  let fix unify_list_elements
      (fuel' : nat)
      (ptrns_orig actuals_orig : list norm_type)
      (subst0 : type_subst)
      (ptrns0 actuals0 : list norm_type)
      {struct ptrns0}
      : result type_subst :=
      match ptrns0, actuals0 with
      | [], [] => Ok subst0
      | ptrn0 :: ptrn_rest, actual0 :: actual_rest =>
          match unify_norm_type_fuel fuel' subst0 ptrn0 actual0 with
          | Err e => Err e
          | Ok subst1 =>
              unify_list_elements
                  fuel' ptrns_orig actuals_orig subst1 ptrn_rest actual_rest
          end
      | _, _ => Err (TypeErr_ListMismatch ptrns_orig actuals_orig)
      end
  in
  let fix find_and_remove_map_entry
      (ptrn_key : norm_type)
      (actual_entries : list (norm_type * norm_type))
      {struct actual_entries}
      : option (norm_type * list (norm_type * norm_type)) :=
      match actual_entries with
      | [] => None
      | (actual_key, actual_value) :: actual_rest =>
          if norm_type_beq ptrn_key actual_key then
            Some (actual_value, actual_rest)
          else
            match
              find_and_remove_map_entry ptrn_key actual_rest
            with
            | None => None
            | Some (found_value, remaining_entries) =>
                Some (found_value, (actual_key, actual_value) :: remaining_entries)
            end
      end
  in
  let fix unify_map_entries
      (fuel' : nat)
      (ptrn_map_orig actual_map_orig :
         list (norm_type * norm_type))
      (subst0 : type_subst)
      (ptrn_entries actual_entries :
         list (norm_type * norm_type))
      {struct ptrn_entries}
      : result type_subst :=
      match ptrn_entries with
      | [] => Ok subst0
      | (ptrn_key, ptrn_value) :: ptrn_rest =>
          if norm_type_contains_hole ptrn_key then
            Err (TypeErr_HoleInMapPatternKey  ptrn_key)
          else
            match
              find_and_remove_map_entry ptrn_key actual_entries
            with
            | None => 
                Err
                  (TypeErr_Mismatch
                     (NT_Map ptrn_map_orig)
                     (NT_Map actual_map_orig))
            | Some (actual_value, actual_rest) =>
                match
                  unify_norm_type_fuel
                    fuel'
                    subst0
                    ptrn_value
                    actual_value
                with
                | Err e => Err e
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
  | 0 => Err InternalErr_UnificationFuelExhausted
  | S fuel' =>
    if norm_type_contains_hole actual then
      Err (TypeErr_UseHole actual)
    else
      match ptrn with
      | NT_Hole X =>
          match type_hole_lookup subst X with
          | Some T =>
              if norm_type_beq T actual then
                Ok subst
              else
                Err (TypeErr_Mismatch T actual)
          | None =>
              Ok ((X, actual) :: subst)
          end
      | NT_Elem e1 =>
          match actual with
          | NT_Elem e2 =>
              if eqb e1 e2 then
                Ok subst
              else
                Err (TypeErr_Mismatch ptrn actual)
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | NT_Prim p1 =>
          match actual with
          | NT_Prim p2 =>
              if prim_beq p1 p2 then
                Ok subst
              else
                Err (TypeErr_Mismatch ptrn actual)
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | NT_TRep ptrn1 =>
          match actual with
          | NT_TRep actual1 =>
              unify_norm_type_fuel fuel' subst ptrn1 actual1
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | NT_Unit => 
          match actual with
          | NT_Unit => Ok subst
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | NT_Prod ptrn1 ptrn2 ptrn_rest =>
          match actual with
          | NT_Prod actual1 actual2 actual_rest =>
              let ptrn_args :=
                ptrn1 :: ptrn2 :: ptrn_rest
              in
              let actual_args :=
                actual1 :: actual2 :: actual_rest
              in
              unify_list_elements
                fuel'
                ptrn_args
                actual_args
                subst
                ptrn_args
                actual_args

          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | NT_Comb ptrn_name ptrn_args =>
          match actual with
          | NT_Comb actual_name actual_args =>
              if eqb ptrn_name actual_name then
                unify_list_elements
                  fuel'
                  ptrn_args
                  actual_args
                  subst
                  ptrn_args
                  actual_args
              else
                Err (TypeErr_Mismatch ptrn actual)
          | _ => Err (TypeErr_Mismatch ptrn actual)
          end
      | NT_Map ptrn_entries =>
          match actual with
          | NT_Map actual_entries =>
              match find_duplicate_map_key [] ptrn_entries with
              | Some duplicate_key =>
                  Err
                    (TypeErr_DuplicateMapPatternKey duplicate_key)
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

Definition unify_norm_type
    (subst : type_subst)
    (ptrn actual : norm_type)
  : result type_subst :=
  unify_norm_type_fuel (S (norm_type_size ptrn)) subst ptrn actual.

Fixpoint unify_norm_type_list_aux
    (subst : type_subst)
    (ptrns actuals : list norm_type)
    (original_ptrns original_actuals :
       list norm_type)
    {struct ptrns}
  : result type_subst :=
  match ptrns, actuals with
  | [], [] => Ok subst
  | ptrn :: ptrn_rest,
    actual :: actual_rest =>
      subst' <-
        unify_norm_type subst ptrn actual ;;
      unify_norm_type_list_aux
        subst'
        ptrn_rest
        actual_rest
        original_ptrns
        original_actuals
  | _, _ =>
      Err
        (TypeErr_ListMismatch original_ptrns original_actuals)
  end.

Definition unify_norm_type_list
    (subst : type_subst)
    (ptrns actuals : list norm_type)
  : result type_subst :=
  unify_norm_type_list_aux
    subst
    ptrns
    actuals
    ptrns
    actuals.

Fixpoint holenames_in_subst_lookup
    (holenames : list string)
    (subst : type_subst)
  : result (list norm_type) :=
  match holenames with
  | [] => Ok []
  | X :: rest =>
      match type_hole_lookup subst X with
      | None => Err (Err_UnboundHole X)
      | Some T =>
          Ts <- holenames_in_subst_lookup rest subst ;;
          Ok (T :: Ts)
      end
  end.

Definition infer_comb_type_decl_info
      (f : type_context -> core_expr -> result norm_type)
      (Gamma0 : type_context)
      (ctor : core_expr)
      : result (TypeName * norm_type * list string * list norm_type) :=
      match f Gamma0 ctor with
      | Err e => Err e
      | Ok ctortype =>
          match normal_type_comb_lookup Gamma0 ctortype with
          | None => Err TypeErr_UnknownCombSignature
          | Some (tn, declared_ctor_type, holenames, argsptrn) =>
              Ok (tn, declared_ctor_type, holenames, argsptrn)
          end
      end.

Definition infer_comb_type_info
      (f : type_context -> core_expr -> result norm_type)
      (Gamma0 : type_context)
      (ctor : core_expr) 
      (arglst : list core_expr)
      : result (TypeName * norm_type * list norm_type * list norm_type) :=
  decl_info <- infer_comb_type_decl_info f Gamma0 ctor ;;
  let '(tn, ctortype, holenames, argsptrn) := decl_info in
  argtypes <- infer_list f Gamma0 arglst ;;
  argsubst <- unify_norm_type_list [] argsptrn argtypes ;;
  typeargs <- holenames_in_subst_lookup holenames argsubst ;;
  Ok (tn, ctortype, typeargs, argtypes).

Definition infer_comb_prim_app
      (f : type_context -> core_expr -> result norm_type)
      (Gamma : type_context)
      (ctor : core_expr)
      (arglst : list core_expr)
      (prm : prim)
      : result norm_type :=
  info <- infer_comb_type_info f Gamma ctor arglst ;;
  let '(_, ctortype, _, argtypes) := info in
  match prm with
  | Prm_Left => Ok ctortype
  | Prm_Right =>
      match argtypes with
      | [] => Ok NT_Unit
      | [x] => Ok x
      | x1 :: x2 :: xs => Ok (NT_Prod x1 x2 xs)
      end
  end.

Definition infer_type_app
    (f : type_context -> core_expr -> result norm_type)
    (Gamma : type_context)
    (a b : core_expr)
    (aty bty : norm_type)
  : result norm_type :=
  match a, aty, b, bty with
  | CE_Comb ctor arglst, _, (CE_Prim prm), _ =>
      infer_comb_prim_app f Gamma ctor arglst prm
  | _, NT_Unit, _, NT_Prim _ => Err (TypeErr_InvalidApp aty bty)
  | _, NT_Prod x _ _, _, NT_Prim Prm_Left => Ok x
  | _, NT_Prod _ x2 xs, _, NT_Prim Prm_Right => Ok (last xs x2)
  | _, _, _, _ => Err (TypeErr_InvalidApp aty bty)
  end.

Fixpoint value_key_mem
    (key : value)
    (keys : list value)
  : bool :=
  match keys with
  | [] => false
  | key' :: rest => value_beq key key' || value_key_mem key rest
  end.

Fixpoint infer_type_core_expr
    (Gamma : type_context)
    (tm : core_expr)
    {struct tm}
  : result norm_type :=
  let fix infer_map_entries
    (seen_key_types : list norm_type)
    (entries : list (core_expr * core_expr))
    : result (list (norm_type * norm_type)) :=
    match entries with
    | [] => Ok []
    | (key, val) :: rest =>
        match infer_type_core_expr Gamma key with
        | Err e => Err e
        | Ok normalized_key_type =>
            if norm_type_mem normalized_key_type seen_key_types
            then Err (TypeErr_DuplicateMapKey normalized_key_type)
            else
              match infer_type_core_expr Gamma val with
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
  in
  match tm with
  | CE_Elem e => Ok (NT_Elem e)
  | CE_Prim p => Ok (NT_Prim p)
  | CE_TRep T =>
      TN <- normalize_core_type T ;;
      if norm_type_contains_hole TN then
        Err (ExprErr_UseHole tm)
      else
        Ok (NT_TRep TN)
  | CE_Prod lst =>
      match
        infer_list infer_type_core_expr Gamma lst
      with
      | Err e => Err e
      | Ok [] => Ok NT_Unit
      | Ok [y] => Err (ExprErr_InvalidProd tm)
      | Ok (y1 :: y2 :: ys) => Ok (NT_Prod y1 y2 ys)
      end
  | CE_Comb ctor arglst =>
      match infer_comb_type_info infer_type_core_expr Gamma ctor arglst with
      | Err e => Err e
      | Ok (tn, _, typeargs, _) =>
          let trep_replace (T : norm_type) : norm_type :=
              match T with
              | NT_TRep T1 => T1
              | _ => T
              end
          in
          Ok (NT_Comb tn (map trep_replace typeargs))
      end
  | CE_Map entries =>
      entry_types <- infer_map_entries [] entries ;;
      Ok (NT_Map entry_types)
  | CE_App a b =>
      ta <- infer_type_core_expr Gamma a ;;
      tb <- infer_type_core_expr Gamma b ;;
       infer_type_app infer_type_core_expr Gamma a b ta tb
  end. 

Fixpoint eval_core_expr
    (tm : core_expr)
    {struct tm}
  : result value :=
  match tm with
  | CE_Elem e => Ok (V_Elem e)
  | CE_Prim p => Ok (V_Prim p)
  | CE_TRep T =>
      TN <- normalize_core_type T ;;
      if norm_type_contains_hole TN then
        Err (ExprErr_UseHole tm)
      else
        Ok (V_TRep TN)
  | CE_Prod es =>
      match es with
      | [] => Ok V_Unit
      | [e] => Err (ExprErr_InvalidProd tm)
      | _ =>
          vs <- eval_core_expr_list eval_core_expr es ;;
          Ok (V_Prod vs)
      end
  | CE_Comb ctor args =>
      ctor_value <- eval_core_expr ctor ;;
      arg_values <- eval_core_expr_list eval_core_expr args ;;
      Ok (V_Comb ctor_value arg_values)
  | CE_Map entries =>
      let fix eval_map_entries
          (seen_keys : list value)
          (xs : list (core_expr * core_expr))
          : result (list (value * value)) :=
          match xs with
          | [] => Ok []
          | (key_expr, val_expr) :: rest =>
              key_value <- eval_core_expr key_expr ;;
              if value_key_mem key_value seen_keys then
                Err (ExprErr_DuplicateMapKey key_expr)
              else
                val_value <- eval_core_expr val_expr ;;
                rest_values <- eval_map_entries (key_value :: seen_keys) rest ;;
                Ok ((key_value, val_value) :: rest_values)
          end
      in
      match eval_map_entries [] entries with
      | Err e =>
          Err e
      | Ok values =>
          Ok (V_Map values)
      end
  | CE_App a b =>
      match eval_core_expr a with
      | Err e => Err e
      | Ok va =>
          match eval_core_expr b with
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

Fixpoint norm_type_contains_named_hole
    (X : string)
    (T : norm_type)
  : bool :=
  match T with
  | NT_Hole Y => eqb X Y
  | NT_Elem _ => false
  | NT_Prim _ => false
  | NT_Unit => false
  | NT_TRep T1 =>
      norm_type_contains_named_hole X T1
  | NT_Prod T1 T2 Ts =>
      existsb (norm_type_contains_named_hole X) (T1 :: T2 :: Ts)
  | NT_Comb _ Ts =>
      existsb (norm_type_contains_named_hole X) Ts
  | NT_Map entries =>
      existsb
        (fun entry =>
           let '(K, V) := entry in
           norm_type_contains_named_hole X K
           || norm_type_contains_named_hole X V)
        entries
  end.

Definition hole_occurs_in_norm_types
    (X : string)
    (Ts : list norm_type)
  : bool :=
  existsb (norm_type_contains_named_hole X) Ts.

Fixpoint validate_declared_holes_used
    (holenames : list string)
    (args : list norm_type)
  : result unit :=
  match holenames with
  | [] =>
      Ok tt
  | X :: rest =>
      if hole_occurs_in_norm_types X args then
        validate_declared_holes_used rest args
      else
        Err (TypeErr_DeclaredHoleNotUsed X)
  end.

Definition holename_mem
    (X : string)
    (holenames : list string)
  : bool :=
  existsb (fun Y => eqb X Y) holenames.

Fixpoint validate_norm_type_holes_declared
    (holenames : list string)
    (T : norm_type)
  : result unit :=
  let fix validate_core_types (Ts : list norm_type) : result unit :=
      match Ts with
      | [] => Ok tt
      | T1 :: rest =>
          match
            validate_norm_type_holes_declared holenames T1 with
          | Err e => Err e
          | Ok _ => validate_core_types rest
          end
      end
  in
  let fix validate_entries (entries : list (norm_type * norm_type)) : result unit :=
      match entries with
      | [] => Ok tt
      | (K, V) :: rest =>
          _ <- validate_norm_type_holes_declared holenames K ;;
          _ <- validate_norm_type_holes_declared holenames V ;;
          validate_entries rest
      end
  in
  match T with
  | NT_Hole X =>
      if holename_mem X holenames then
        Ok tt
      else
        Err (TypeErr_UndeclaredHole X)
  | NT_Elem _ => Ok tt
  | NT_Prim _ => Ok tt
  | NT_Unit => Ok tt
  | NT_TRep T1 => validate_norm_type_holes_declared holenames T1
  | NT_Prod T1 T2 Ts => validate_core_types (T1 :: T2 :: Ts)
  | NT_Comb _ Ts => validate_core_types Ts
  | NT_Map entries => validate_entries entries
  end.

Fixpoint validate_argument_holes_declared
    (holenames : list string)
    (args : list norm_type)
  : result unit :=
  match args with
  | [] => Ok tt
  | T :: rest =>
      _ <- validate_norm_type_holes_declared holenames T ;;
      validate_argument_holes_declared holenames rest
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

Definition validate_hole_declaration (holenames : list string) (args : list norm_type)
  : result unit :=
  _ <- validate_unique_holenames holenames ;;
  _ <- validate_declared_holes_used holenames args ;;
  validate_argument_holes_declared holenames args.

Definition exec_core_command
    (st : machine_state)
    (cmd : core_command)
  : result machine_state :=
  let Gamma := ms_type_ctx st in
  match cmd with
  | CC_DeclCombVariant tn ctortype holenames args =>
      if comb_type_closed Gamma tn then
        Err (TypeErr_CombClosed tn)
      else
        match normalize_core_type ctortype with
        | Err e => Err e
        | Ok nrmctortype =>
            if norm_type_contains_hole nrmctortype then
              Err (TypeErr_UseHole nrmctortype)
            else
            if norm_type_contains_prim nrmctortype then
              Err (TypeErr_UsePrimInDeclCombCtor nrmctortype)
            else
              match validate_map_pattern_keys nrmctortype with
              | Err e => Err e
              | Ok _ =>
                  match normal_type_comb_lookup Gamma nrmctortype with
                  | Some (oldtn, _, _, _) =>
                      Err (TypeErr_DuplicateCombSignature oldtn nrmctortype)
                  | None =>
                      nrmargs <- normalize_core_type_list args ;;
                      if existsb norm_type_contains_prim nrmargs then
                        Err (TypeErr_UsePrimInDeclCombParam nrmargs)
                      else
                        _ <- validate_hole_declaration holenames nrmargs ;;
                        _ <- validate_list validate_map_pattern_keys nrmargs ;;
                        Ok
                          {| ms_type_ctx :=
                               BindCombType tn nrmctortype holenames nrmargs
                               :: Gamma;
                             ms_last_type := ms_last_type st;
                             ms_last_value := ms_last_value st |}
                  end
              end
        end
  | CC_Eval e =>
      T <- infer_type_core_expr Gamma e ;;
      v <- eval_core_expr e ;;
      Ok
        {| ms_type_ctx := Gamma;
           ms_last_type := T;
           ms_last_value := v |}
  | CC_CloseCombType tn =>
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

Definition type_def_context : Type := list (TypeName * core_type).
Definition expr_def_context : Type := list (VarName * core_expr).

Fixpoint lookup_type_def
    (Delta : type_def_context)
    (X : TypeName)
  : option core_type :=
  match Delta with
  | [] => None
  | (Y, T) :: rest =>
      if eqb X Y then Some T else lookup_type_def rest X
  end.

Fixpoint lookup_expr_def
    (Sigma : expr_def_context)
    (X : VarName)
  : option core_expr :=
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

Inductive TypeNameKind : Type :=
  | TNK_Abbr
  | TNK_Comb.

Definition type_name_context : Type :=
  list (TypeName * TypeNameKind).

Fixpoint lookup_type_name_kind
    (Theta : type_name_context)
    (X : TypeName)
  : option TypeNameKind :=
  match Theta with
  | [] => None
  | (Y, kind) :: rest =>
      if eqb X Y then
        Some kind
      else
        lookup_type_name_kind rest X
  end.

Record elaboration_state : Type := {
  es_expr_defs : expr_def_context;
  es_type_defs : type_def_context;
  es_type_names : type_name_context
}.

Definition initial_elaboration_state : elaboration_state :=
  {| es_expr_defs := [];
     es_type_defs := [];
     es_type_names := [] |}.

Record elaborated_command : Type := {
  ec_elaboration_state : elaboration_state;
  ec_core_command : option core_command
}.

Fixpoint elaborate_type
    (Delta : type_def_context)
    (Theta : type_name_context)
    (T : source_type)
    {struct T}
  : result core_type :=
  let fix elaborate_entries
      (entries : list (source_type * source_type))
      : result (list (core_type * core_type)) :=
      match entries with
      | [] =>
          Ok []
      | (K, V) :: rest =>
          K' <- elaborate_type Delta Theta K ;;
          V' <- elaborate_type Delta Theta V ;;
          rest' <- elaborate_entries rest ;;
          Ok ((K', V') :: rest')
      end
  in
  match T with
  | ST_Hole X => Ok (CT_Hole X)
  | ST_Abbr X =>
      match lookup_type_def Delta X with
      | None => Err (Err_UnboundTypeAbbr X)
      | Some T' => Ok T'
      end
  | ST_Elem e => Ok (CT_Elem e)
  | ST_Prim p => Ok (CT_Prim p)
  | ST_TRep T1 =>
      T1' <- elaborate_type Delta Theta T1 ;;
      Ok (CT_TRep T1')
  | ST_Prod Ts =>
      Ts' <- map_result (elaborate_type Delta Theta) Ts ;;
      Ok (CT_Prod Ts')
  | ST_Comb tn Ts =>
    match lookup_type_name_kind Theta tn with
    | Some TNK_Comb =>
        Ts' <- map_result (elaborate_type Delta Theta) Ts ;;
        Ok (CT_Comb tn Ts')
    | Some TNK_Abbr =>
        Err (TypeErr_ExpectedCombType tn)
    | None =>
        Err (TypeErr_UnknownCombType tn)
    end
  | ST_Map entries =>
      entries' <- elaborate_entries entries ;;
      Ok (CT_Map entries')
  end.

Fixpoint elaborate_expr
    (Sigma : expr_def_context)
    (Delta : type_def_context)
    (Theta : type_name_context)
    (e : source_expr)
    {struct e}
  : result core_expr :=
  let fix elaborate_exprs
      (es : list source_expr)
      : result (list core_expr) :=
      match es with
      | [] => Ok []
      | e1 :: rest =>
          e1' <- elaborate_expr Sigma Delta Theta e1 ;;
          rest' <- elaborate_exprs rest ;;
          Ok (e1' :: rest')
      end
  in
  let fix elaborate_entries
      (entries : list (source_expr * source_expr))
      : result (list (core_expr * core_expr)) :=
      match entries with
      | [] => Ok []
      | (K, V) :: rest =>
          K' <- elaborate_expr Sigma Delta Theta K ;;
          V' <- elaborate_expr Sigma Delta Theta V ;;
          rest' <- elaborate_entries rest ;;
          Ok ((K', V') :: rest')
      end
  in
  match e with
  | SE_Var X =>
      match lookup_expr_def Sigma X with
      | None => Err (Err_UnboundVar X)
      | Some e' => Ok e'
      end
  | SE_Elem x => Ok (CE_Elem x)
  | SE_Prim p => Ok (CE_Prim p)
  | SE_TRep T =>
      T' <- elaborate_type Delta Theta T ;;
      Ok (CE_TRep T')
  | SE_Prod es =>
      es' <- elaborate_exprs es ;;
      Ok (CE_Prod es')
  | SE_Comb ctor args =>
      ctor' <- elaborate_expr Sigma Delta Theta ctor ;;
      args' <- elaborate_exprs args ;;
      Ok (CE_Comb ctor' args')
  | SE_Map entries =>
      entries' <- elaborate_entries entries ;;
      Ok (CE_Map entries')
  | SE_App a b =>
      a' <- elaborate_expr Sigma Delta Theta a ;;
      b' <- elaborate_expr Sigma Delta Theta b ;;
      Ok (CE_App a' b')
  end.

Definition elaborate_command
    (est : elaboration_state)
    (cmd : source_command)
  : result elaborated_command :=
  let Sigma := es_expr_defs est in
  let Delta := es_type_defs est in
  let Theta := es_type_names est in
  match cmd with
  | SC_DeclVar X rhs =>
      if expr_def_declared Sigma X then
        Err (Err_DuplicateVar X)
      else
        rhs' <- elaborate_expr Sigma Delta Theta rhs ;;
        Ok
          {| ec_elaboration_state :=
               {| es_expr_defs := (X, rhs') :: Sigma;
                  es_type_defs := Delta;
                  es_type_names := Theta |};
             ec_core_command := None |}

  | SC_NewTypeAbbr X T =>
      match lookup_type_name_kind Theta X with
      | Some _ =>
          Err (TypeErr_DuplicateType X)
      | None =>
          T' <- elaborate_type Delta Theta T ;;
          Ok
            {| ec_elaboration_state :=
                 {| es_expr_defs := Sigma;
                    es_type_defs := (X, T') :: Delta;
                    es_type_names := (X, TNK_Abbr) :: Theta |};
               ec_core_command := None |}
      end

  | SC_DeclCombVariant tn ctor holenames args =>
      Theta' <-
        match lookup_type_name_kind Theta tn with
        | None => Ok ((tn, TNK_Comb) :: Theta)
        | Some TNK_Comb => Ok Theta
        | Some TNK_Abbr => Err (TypeErr_DuplicateType tn)
        end ;;
      ctor' <- elaborate_type Delta Theta' ctor ;;
      args' <- map_result (elaborate_type Delta Theta') args ;;
      Ok
        {| ec_elaboration_state :=
             {| es_expr_defs := Sigma;
                es_type_defs := Delta;
                es_type_names := Theta' |};
           ec_core_command :=
             Some
               (CC_DeclCombVariant
                  tn
                  ctor'
                  holenames
                  args') |}

  | SC_CloseCombType tn =>
      match lookup_type_name_kind Theta tn with
      | Some TNK_Comb =>
          Ok
            {| ec_elaboration_state := est;
               ec_core_command := Some (CC_CloseCombType tn) |}
      | Some TNK_Abbr =>
          Err (TypeErr_CloseUnknownComb tn)
      | None =>
          Err (TypeErr_CloseUnknownComb tn)
      end

  | SC_Eval e =>
      e' <- elaborate_expr Sigma Delta Theta e ;;
      Ok
        {| ec_elaboration_state := est;
           ec_core_command := Some (CC_Eval e') |}
  end.

Fixpoint run_source_prog_aux
    (est : elaboration_state)
    (mst : machine_state)
    (prg : source_prog)
    {struct prg}
  : result machine_state :=
  match prg with
  | [] =>
      Ok mst
  | cmd :: rest =>
      ec <- elaborate_command est cmd ;;
      match ec_core_command ec with
      | None =>
          run_source_prog_aux
            (ec_elaboration_state ec)
            mst
            rest
      | Some core_cmd =>
          mst' <- exec_core_command mst core_cmd ;;
          run_source_prog_aux
            (ec_elaboration_state ec)
            mst'
            rest
      end
  end.

Record Prg_Result : Type := {
  prog_type : norm_type;
  prog_val : value
}.

Definition run_prog
    (input_program : source_prog)
  : result Prg_Result :=
  st <-
    run_source_prog_aux initial_elaboration_state initial_state input_program ;;
  Ok
    {| prog_type := ms_last_type st;
       prog_val := ms_last_value st |}.

