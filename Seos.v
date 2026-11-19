(* Kodozit.Seos Formal Theory @ Paraxenoman *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope bool_scope.

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

Inductive type : Type :=
  | T_Hole : string -> type
  | T_Abbr : TypeName -> type
  | T_Elem : elem -> type
  | T_Prim : prim -> type
  | T_TRep : type -> type
  | T_Prod : list type -> type
  | T_Comb : TypeName -> list type -> type.

Inductive expr : Type :=
  | E_Var : VarName -> expr
  | E_Elem : elem -> expr
  | E_Prim : prim -> expr
  | E_TRep : type -> expr
  | E_Prod : list expr -> expr
  | E_Comb : expr -> list expr -> expr
  | E_App : expr -> expr -> expr.

Inductive value : Type :=
  | V_Elem : elem -> value
  | V_Prim : prim -> value
  | V_TRep : type -> value
  | V_Prod : list value -> value
  | V_Comb : value -> list value -> value.

Inductive command : Type :=
  | C_DeclVar : VarName -> expr -> command
  | C_NewTypeAbbr : TypeName -> type -> command
  | C_DeclCombVariant : TypeName -> type -> list string -> list type -> command
  | C_CloseCombType : TypeName -> command
  | C_Eval : expr -> command.

Inductive error : Type :=
  | Err_NotImplemented : error
  | Err_UnboundVar : VarName -> error
  | Err_UnboundType : TypeName -> error
  | Err_UnboundTypeAbbr : TypeName -> error
  | Err_UnboundHole : string -> error
  | Err_DuplicateVar : VarName -> error
  | Err_DuplicateType : TypeName -> error
  | Err_DuplicateCombSignature : TypeName -> type -> error
  | Err_UnknownCombSignature : error
  | Err_InvalidType : error
  | Err_CyclicTypeAbbr : TypeName -> error
  | Err_TypeMismatch : type -> type -> error
  | Err_UnexpandedVar : VarName -> error
  | Err_CombTypeClosed : TypeName -> error
  | Err_CloseUnknownCombType : TypeName -> error
  | Err_CombTypeAlreadyClosed : TypeName -> error
  | Err_TypeListMismatch : list type -> list type -> error
  | Err_UsePrimInDeclComb : type -> error
  | Err_UseHoleInExpr : expr -> error
  | TypeErr_InvalidApp : type -> type -> error
  | ExprErr_InvalidApp : expr -> expr -> error.

Inductive result (A : Type) : Type :=
  | Ok : A -> result A
  | Err : error -> result A.

Arguments Ok {A} _.
Arguments Err {A} _.

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
  | _ => false
  end.

Fixpoint contains_hole (T : type) : bool :=
  match T with
  | T_Hole _ => true
  | T_TRep T1 => contains_hole T1
  | T_Prod Ts => existsb contains_hole Ts
  | T_Comb _ Ts => existsb contains_hole Ts
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

Definition typename_mem (X : TypeName) (xs : list TypeName) : bool :=
  existsb (fun Y => eqb X Y) xs.

Record machine_state : Type := {
  ms_type_ctx : type_context;
  ms_last_type : type;
  ms_last_value : value
}.

Definition initial_state : machine_state :=
  {| ms_type_ctx := [];
     ms_last_type := T_Unit;
     ms_last_value := V_Unit |}.

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
  | _, _ => false
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
    (visited : list TypeName)
    (Gamma : type_context)
    (T : type)
  : result type :=
  match fuel with
  | 0 => Err Err_InvalidType
  | S fuel' =>
      let fix norm_types (Ts : list type) : result (list type) :=
          match Ts with
          | [] => Ok []
          | T1 :: rest =>
              match norm_type_fuel fuel' visited Gamma T1 with
              | Err e => Err e
              | Ok T1N =>
                  match norm_types rest with
                  | Err e => Err e
                  | Ok restN => Ok (T1N :: restN)
                  end
              end
          end
      in
      match T with
      | T_Hole X => Ok (T_Hole X)
      | T_Elem e => Ok (T_Elem e)
      | T_Prim p => Ok (T_Prim p)
      | T_Abbr X =>
          if typename_mem X visited then
            Err (Err_CyclicTypeAbbr X)
          else
            match type_abbr_lookup Gamma X with
            | None => Err (Err_UnboundTypeAbbr X)
            | Some T' =>
                norm_type_fuel fuel' (X :: visited) Gamma T'
            end
      | T_TRep T1 =>
          match norm_type_fuel fuel' visited Gamma T1 with
          | Err e => Err e
          | Ok T1N => Ok (T_TRep T1N)
          end
      | T_Prod Ts =>
          match norm_types Ts with
          | Err e => Err e
          | Ok [] => Ok T_Unit
          | Ok [T1] => Ok T1
          | Ok TsN => Ok (T_Prod TsN)
          end
      | T_Comb X Ts =>
          match norm_types Ts with
          | Err e => Err e
          | Ok TsN => Ok (T_Comb X TsN)
          end
      end
  end.

Definition norm_type (Gamma : type_context) (T : type) : result type :=
  norm_type_fuel
    (S (type_size T + type_context_size Gamma))
    []
    Gamma
    T.

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
            Err (Err_UsePrimInDeclComb tN)
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

Definition value_beq
    (type_eq : type -> type -> result bool)
    (value_eq : value -> value -> bool)
    (v1 v2 : value)
  : result bool :=
  match v1, v2 with
  | V_Elem e1, V_Elem e2 => Ok (eqb e1 e2)
  | V_Prim p1, V_Prim p2 => Ok (prim_beq p1 p2)
  | V_TRep T1, V_TRep T2 => type_eq T1 T2
  | V_Prod vs1, V_Prod vs2 => Ok (list_eqb value_eq vs1 vs2)
  | V_Comb ctor1 args1, V_Comb ctor2 args2 =>
      Ok (value_eq ctor1 ctor2 && list_eqb value_eq args1 args2)
  | _, _ => Ok false
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
  match fuel with
  | 0 => Err Err_InvalidType
  | S fuel' =>
      match ptrn with
      | T_Hole X =>
          match type_hole_lookup subst X with
          | Some T =>
              if type_beq T actual then
                Ok subst
              else
                Err (Err_TypeMismatch T actual)
          | None => Ok ((X, actual) :: subst)
          end
      | T_Abbr X =>
          match actual with
          | T_Abbr Y =>
              if eqb X Y then
                Ok subst
              else
                Err (Err_TypeMismatch ptrn actual)
          | _ => Err (Err_TypeMismatch ptrn actual)
          end
      | T_Elem e1 =>
          match actual with
          | T_Elem e2 =>
              if eqb e1 e2 then
                Ok subst
              else
                Err (Err_TypeMismatch ptrn actual)
          | _ => Err (Err_TypeMismatch ptrn actual)
          end
      | T_Prim p1 =>
          match actual with
          | T_Prim p2 =>
              if prim_beq p1 p2 then
                Ok subst
              else
                Err (Err_TypeMismatch ptrn actual)
          | _ => Err (Err_TypeMismatch ptrn actual)
          end
      | T_TRep ptrn1 =>
          match actual with
          | T_TRep actual1 =>
              unify_type_fuel fuel' subst ptrn1 actual1
          | _ => Err (Err_TypeMismatch ptrn actual)
          end
      | T_Prod ptrns =>
          match actual with
          | T_Prod actuals =>
              let fix unify_product_elements
                  (subst0 : type_subst)
                  (ptrns0 actuals0 : list type)
                  {struct ptrns0}
                  : result type_subst :=
                  match ptrns0, actuals0 with
                  | [], [] => Ok subst0
                  | ptrn0 :: ptrn_rest, actual0 :: actual_rest =>
                      match
                        unify_type_fuel fuel' subst0 ptrn0 actual0
                      with
                      | Err e => Err e
                      | Ok subst1 =>
                          unify_product_elements
                            subst1
                            ptrn_rest
                            actual_rest
                      end
                  | _, _ =>
                      Err (Err_TypeListMismatch ptrns actuals)
                  end
              in
              unify_product_elements subst ptrns actuals
          | _ => Err (Err_TypeMismatch ptrn actual)
          end
      | T_Comb ptrn_name ptrn_args =>
          match actual with
          | T_Comb actual_name actual_args =>
              if eqb ptrn_name actual_name then
                let fix unify_comb_arguments
                    (subst0 : type_subst)
                    (ptrns0 actuals0 : list type)
                    {struct ptrns0}
                    : result type_subst :=
                    match ptrns0, actuals0 with
                    | [], [] => Ok subst0
                    | ptrn0 :: ptrn_rest, actual0 :: actual_rest =>
                        match
                          unify_type_fuel fuel' subst0 ptrn0 actual0
                        with
                        | Err e => Err e
                        | Ok subst1 =>
                            unify_comb_arguments
                              subst1
                              ptrn_rest
                              actual_rest
                        end
                    | _, _ =>
                        Err
                          (Err_TypeListMismatch
                             ptrn_args
                             actual_args)
                    end
                in
                unify_comb_arguments subst ptrn_args actual_args
              else
                Err (Err_TypeMismatch ptrn actual)
          | _ => Err (Err_TypeMismatch ptrn actual)
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
        (Err_TypeListMismatch
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

Definition infer_type_app
    (Gamma : type_context)
    (t pt : type)
  : result type :=
  match t, pt with
  | T_Prod [], T_Prim _ =>
      Err (TypeErr_InvalidApp t pt)
  | T_Prod (x :: _), T_Prim Prm_Left =>
      norm_type Gamma x
  | T_Prod xs, T_Prim Prm_Right =>
      norm_type Gamma (last xs T_Unit)
  | _, _ =>
      Err (TypeErr_InvalidApp t pt)
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

Fixpoint infer_type_expr
    (Gamma : type_context)
    (tm : expr)
    {struct tm}
  : result type :=
  let infer_comb_type_decl_info
      (Gamma0 : type_context)
      (ctor : expr)
      : result (TypeName * type * list string * list type) :=
      match infer_type_expr Gamma0 ctor with
      | Err e => Err e
      | Ok ctortype =>
          match type_comb_lookup Gamma0 ctortype with
          | None => Err Err_UnknownCombSignature
          | Some (tn, declared_ctor_type, holenames, argsptrn) =>
              Ok (tn, declared_ctor_type, holenames, argsptrn)
          end
      end
  in
  let infer_comb_type_info
      (Gamma0 : type_context)
      (ctor : expr)
      (arglst : list expr)
      : result (TypeName * type * list type) :=
      match infer_comb_type_decl_info Gamma0 ctor with
      | Err e => Err e
      | Ok (tn, ctortype, holenames, argsptrn) =>
          match infer_list infer_type_expr Gamma0 arglst with
          | Err e => Err e
          | Ok argtypes =>
              match unify_type_list [] argsptrn argtypes with
              | Err e => Err e
              | Ok argsubst =>
                  match
                    holenames_in_subst_lookup holenames argsubst
                  with
                  | Err e => Err e
                  | Ok typeargs =>
                      Ok (tn, ctortype, typeargs)
                  end
              end
          end
      end
  in
  let infer_comb_prim_app
      (ctor : expr)
      (arglst : list expr)
      (prm : prim)
      : result type :=
      match infer_comb_type_info Gamma ctor arglst with
      | Err e => Err e
      | Ok _ =>
          match infer_type_expr Gamma ctor with
          | Err e => Err e
          | Ok ctortype =>
              match
                infer_list infer_type_expr Gamma arglst
              with
              | Err e => Err e
              | Ok argtypes =>
                  match prm with
                  | Prm_Left => norm_type Gamma ctortype
                  | Prm_Right =>
                      norm_type Gamma (T_Prod argtypes)
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
            Err (Err_UseHoleInExpr tm)
          else
            Ok TN
      end
  | E_Prod [] => Ok T_Unit
  | E_Prod [x] =>
      match infer_type_expr Gamma x with
      | Err e => Err e
      | Ok T => norm_type Gamma T
      end
  | E_Prod (x :: xs) =>
      match
        infer_list infer_type_expr Gamma (x :: xs)
      with
      | Err e => Err e
      | Ok Ts => norm_type Gamma (T_Prod Ts)
      end
  | E_Comb ctor arglst =>
      match infer_comb_type_info Gamma ctor arglst with
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
  | E_App (E_Comb ctor arglst) (E_Prim prm) =>
      infer_comb_prim_app ctor arglst prm
  | E_App a b =>
      match infer_type_expr Gamma a with
      | Err e => Err e
      | Ok ta =>
          match infer_type_expr Gamma b with
          | Err e => Err e
          | Ok tb => infer_type_app Gamma ta tb
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
      | [e] => eval_expr e
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
        Err (Err_DuplicateType X)
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
        Err (Err_CombTypeClosed tn)
      else if type_abbr_declared Gamma tn then
        Err (Err_DuplicateType tn)
      else
        match norm_type Gamma ctortype with
        | Err e => Err e
        | Ok nrmctortype =>
            match type_comb_lookup Gamma nrmctortype with
            | Some (oldtn, _, _, _) =>
                Err
                  (Err_DuplicateCombSignature
                     oldtn
                     nrmctortype)
            | None =>
                if contains_prim nrmctortype then
                  Err
                    (Err_UsePrimInDeclComb
                       nrmctortype)
                else
                  match norm_comb_list Gamma args with
                  | Err e => Err e
                  | Ok nrmargs =>
                      Ok
                        {| ms_type_ctx :=
                             BindCombType
                               tn
                               nrmctortype
                               holenames
                               nrmargs
                             :: Gamma;
                           ms_last_type := ms_last_type st;
                           ms_last_value := ms_last_value st |}
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
        Err (Err_CloseUnknownCombType tn)
      else if comb_type_closed Gamma tn then
        Err (Err_CombTypeAlreadyClosed tn)
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
            match
              unfold_prog_aux
                ((X, rhs') :: Sigma)
                Delta
                rest
            with
            | Err e => Err e
            | Ok rest' =>
                Ok (C_DeclVar X rhs' :: rest')
            end
        end
  | C_NewTypeAbbr X T :: rest =>
      if type_def_declared Delta X then
        Err (Err_DuplicateType X)
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

Fixpoint compile_prog_aux
    (st : machine_state)
    (prg : prog)
    {struct prg}
  : result machine_state :=
  match prg with
  | [] => Ok st
  | cmd :: rest =>
      match exec_command st cmd with
      | Err e => Err e
      | Ok st' => compile_prog_aux st' rest
      end
  end.

Definition compile_prog
    (input_program : prog)
  : result Prg_Result :=
  match unfold_prog input_program with
  | Err e => Err e
  | Ok unfolded_program =>
      match
        compile_prog_aux initial_state unfolded_program
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
  C_DeclVar "oneprod" (E_Prod [E_Elem "bla"]); 
  C_DeclVar "myvar" (E_Prod [E_TRep (T_Prod [T_Elem "one"]); E_Elem "0"; E_Elem "2"; E_Var "oneprod"]);
  C_Eval (E_Prod [E_App (E_Var "myvar") (E_Prim Prm_Left); E_App (E_Var "myvar") (E_Prim Prm_Right)]) ].
Compute (compile_prog example_good_prog0).

(* Хорошая программа -  объявление типов-комбинаций *)
Example example_good_prog2 := [
  C_DeclCombVariant "Bool" (T_Elem "true") [] [];
  C_DeclCombVariant "Bool" (T_Elem "false") [] [];
  C_CloseCombType "Bool";
  C_Eval (E_Comb (E_Elem "true") [])
].
Compute (compile_prog example_good_prog2).

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
Compute (compile_prog example_good_prog3).

(* Хорошая программа - типы комбинаций с параметрами произвольных типов *)
Example example_good_prog4 := [
  C_DeclCombVariant "Foo" (T_Elem "Foo") ["a"; "b"] [T_Hole "a"; T_Hole "b"];
  C_CloseCombType "Foo";
  C_Eval (E_Comb (E_Elem "Foo") [E_Unit; (E_Prim Prm_Left)])
].
Compute (compile_prog example_good_prog4).

(* Хорошая программа - типы комбинаций с параметрами одинаковых типов *)
Example example_good_prog5 := [
  C_DeclCombVariant "Foo" (T_Elem "Foo") ["a"] [T_Hole "a"; T_Hole "a"];
  C_CloseCombType "Foo";
  C_Eval (E_Comb (E_Elem "Foo") [E_Unit; E_Unit])
].
Compute (compile_prog example_good_prog5).

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
Compute (compile_prog example_good_prog6).

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
Compute (compile_prog example_good_prog7).

(* Плохая программа - несоблюдение ограничений типов *)
Example example_bad_prog0 := [
  C_DeclCombVariant "Foo" (T_Elem "Foo") [] [T_Hole "a"; T_Hole "a"];
  C_CloseCombType "Foo";
  C_Eval (E_Comb (E_Elem "Foo") [E_Unit; E_Elem "bla"])
].
Compute (compile_prog example_bad_prog0).

(* Плохая программа - undefined variable bad *)
Example example_bad_prog1 := [
  C_DeclVar "bed" (E_Elem "()"); 
  C_Eval (E_Var "bad")].
Compute (compile_prog example_bad_prog1).

(* Плохая программа - затенение переменных *)
Example example_bad_prog2 := [
  C_DeclVar "input" (E_Elem "bla");
  C_DeclVar "input" (E_Prod [E_Elem "0"; E_Elem "2"; E_Elem "VAL"])
].
Compute (compile_prog example_bad_prog2).

(* Плохая программа - объявление типов и их синонимов с занятыми именами *)
Example example_bad_prog3 : prog := [
  C_NewTypeAbbr "NatZero" (T_Prod [T_Elem "Nat"]);
  C_DeclCombVariant "NatZero" (T_Prod [T_Elem "Zero"; (T_Prod [T_Elem "Nat"])]) [] []
].
Compute (compile_prog example_bad_prog3).

(* Плохая программа - объявление типов комбинаций с одинаковым конструктором данных *)
Example example_bad_prog4 : prog := [
  C_NewTypeAbbr "TP" (T_Prod [T_Elem "Nat"]);
  C_DeclCombVariant "NatZero" (T_Prod [T_Elem "Zero"; T_Elem "Nat"]) [] [];
  C_DeclCombVariant "NatZeroCopy" (T_Prod [T_Elem "Zero"; T_Prod [T_Abbr "TP"]]) [] []
].
Compute (compile_prog example_bad_prog4).

(* Плохая программа - попытка расширить закрытый тип *)
Example example_bad_prog5 : prog := [
  C_DeclCombVariant "Bool" (T_Elem "true") [] [];
  C_DeclCombVariant "Bool" (T_Elem "false") [] [];
  C_CloseCombType "Bool";
  C_DeclCombVariant "Bool" (T_Elem "undef") [] [];
  C_Eval (E_Comb (E_Elem "false") [])
].
Compute (compile_prog example_bad_prog5).

(* Плохая программа - попытка использовать T_Prim в конструкторе данных для типа комбинации 
   в объявлении типа комбинации *)
Example example_bad_prog6 : prog := [
  C_DeclCombVariant "Bar" (T_Prod [T_Elem "a"; T_Prim Prm_Left]) [] []
].
Compute (compile_prog example_bad_prog6).

(* Плохая программа - попытка использовать T_Prim в параметрах типа комбинации 
   в объявлении типа комбинации *)
Example example_bad_prog7 : prog := [
  C_DeclCombVariant "Bar" (T_Elem "a") [] [T_Prod [T_Prim Prm_Left; T_Elem "x"]]
].
Compute (compile_prog example_bad_prog7).

(* Плохая программа - ошибочное применение Prm_Left *)
Example example_good_prog8 := [
  C_DeclVar "myvar" (E_Prod []);
  C_Eval (E_App (E_Var "myvar") (E_Prim Prm_Left))].
Compute (compile_prog example_good_prog8).

(* Плохая программа - закрытие несуществующего типа *)
Example example_good_prog9 := [
  C_CloseCombType "Bool"
].
Compute (compile_prog example_good_prog9).

(* Плохая программа - повторное закрытие типа *)
Example example_good_prog10 := [
  C_DeclCombVariant "Bool" (T_Elem "true") [] [];
  C_DeclCombVariant "Bool" (T_Elem "false") [] [];
  C_CloseCombType "Bool";
  C_CloseCombType "Bool"
].
Compute (compile_prog example_good_prog10).


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
    (Err_TypeMismatch
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
    (Err_TypeMismatch
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
        T_Hole "b"
      ]
    ]
    [
      T_Prod [
        T_Elem "Nat"
      ]
    ]
  =
  Err
    (Err_TypeListMismatch
       [T_Hole "a"; T_Hole "b"]
       [T_Elem "Nat"]).
Proof.
  reflexivity.
Qed.

