(* Kodozit.Seos Formal Theory @ Paraxenoman *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope bool_scope.

(* Функция равенства двух списков *)
Fixpoint list_eqb {A} (feq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 =>
      feq x1 x2 && list_eqb feq t1 t2
  | _, _ => false
  end.

Definition TypeName : Type := string.
Definition VarName : Type := string.
Definition elem : Type := string.

Inductive prim : Type :=
  | Prm_Left : prim
  | Prm_Right : prim.

(* Функция равенства примов *)
Definition prim_beq (p1 p2 : prim) : bool :=
  match p1, p2 with
  | Prm_Left, Prm_Left => true
  | Prm_Right, Prm_Right => true
  | _, _ => false
  end.

(* Синтаксис типов  *)
Inductive type : Type :=
  | T_Hole : string -> type
  | T_Abbr : TypeName -> type
  | T_Elem : elem -> type
  | T_Prim : prim -> type
  | T_TRep : type -> type
  | T_Prod : list type -> type
  | T_Comb : TypeName -> list type -> type.

(* Синтаксис выражений  *)
Inductive expr : Type :=
  | E_Var : VarName -> expr
  | E_Elem : elem -> expr
  | E_Prim : prim -> expr
  | E_TRep : type -> expr
  | E_Prod : list expr -> expr
  | E_Comb : expr -> list expr -> expr
  | E_App : expr -> expr -> expr.

(* Синтаксис значений *)
Inductive value : Type :=
  | V_Elem : elem -> value
  | V_Prim : prim -> value
  | V_TRep : type -> value
  | V_Prod : list value -> value
  | V_Comb : value -> list value -> value.

(* Синтаксис комманд *)
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
  | Err_TypeMismatch : type -> type -> error
  | Err_UnexpectedVar : VarName -> error
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
  | BindVarType : VarName -> type -> TypeBinding
  | BindCombType : TypeName -> type -> list string -> list type -> TypeBinding
  | CloseCombType : TypeName -> TypeBinding.

(* Контекст типизации *)
Definition type_context := list TypeBinding.

(* Функция поиска типа по его синониму (аббревиатуре) *)
Fixpoint type_abbr_lookup (Γ : type_context) (X : TypeName) : option type :=
  match Γ with
  | [] => None
  | (BindTypeAbbr Y T) :: rest => 
      if eqb X Y then 
        Some T 
      else 
        type_abbr_lookup rest X
  | _ :: rest => type_abbr_lookup rest X
  end.

(* Функция поиска типа переменной в контексте *)
Fixpoint var_type_lookup (Γ : type_context) (x : VarName) : option type :=
  match Γ with
  | [] => None
  | (BindVarType y T) :: rest => 
      if eqb x y then
        Some T 
      else 
        var_type_lookup rest x
  | _ :: rest => var_type_lookup rest x
  end.

Inductive VarValueBinding : Type :=
  | BindVarValue : VarName -> value -> VarValueBinding.

(* Контекст вычислений *)
Definition eval_context := list VarValueBinding.

(* Функция поиска значения переменной в контексте вычислений *)
Fixpoint var_value_lookup (Sigma : eval_context) (x : VarName) : option value :=
  match Sigma with
  | [] => None
  | (BindVarValue y v1) :: rest => 
      if eqb x y then
        Some v1 
      else 
        var_value_lookup rest x
  end.

Fixpoint eval_expr_list 
        (f : eval_context -> expr -> result value) 
        (ctx : eval_context)
        (ts : list expr) 
        : result (list value) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      match f ctx t with
      | Ok v => 
          match (eval_expr_list f ctx rest) with
          | Ok lt => Ok (v :: lt)
          | Err e => Err e
          end
      | Err e => Err e
      end
  end.

Fixpoint norm_list 
      (f : type_context -> type -> result type) 
      (Γ : type_context) 
      (ts : list type) 
      : result (list type) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
    match f Γ t with
    | Ok nrmpt =>
        match norm_list f Γ rest with
        | Ok nrmpts => Ok (nrmpt :: nrmpts)
        | Err e => Err e
        end
    | Err e => Err e
    end
  end.

Fixpoint contains_prim (T : type) : bool :=
  match T with
  | T_Prim _ => true
  | T_TRep T => contains_prim T
  | T_Prod Ts => existsb contains_prim Ts
  | T_Comb _ Ts => existsb contains_prim Ts
  | _ => false
  end.


Fixpoint norm_comb_list 
      (f : type_context -> type -> result type) 
      (Γ : type_context) 
      (ts : list type) 
      : result (list type) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
    match f Γ t with
    | Ok nrmpt =>
      if contains_prim nrmpt then
        Err (Err_UsePrimInDeclComb nrmpt)
      else
        match norm_comb_list f Γ rest with
        | Ok nrmpts => Ok (nrmpt :: nrmpts)
        | Err e => Err e
        end
    | Err e => Err e
    end
  end.

Record machine_state := {
  ms_type_ctx : type_context;
  ms_eval_ctx : eval_context;
  ms_last_type : type;
  ms_last_value : value
}.

Definition initial_state : machine_state :=
  {| ms_type_ctx := [];
     ms_eval_ctx := [];
     ms_last_type := T_Unit;
     ms_last_value := V_Unit |}.

(* Функция булевого равенства для типов без нормализации *)
Fixpoint type_beq (it1 it2 : type) : bool := 
  match it1, it2 with
  | T_Abbr vn1, T_Abbr vn2 => eqb vn1 vn2
  | T_Elem e1, T_Elem e2 => eqb e1 e2
  | T_Prim p1, T_Prim p2 => prim_beq p1 p2
  | T_TRep tp1, T_TRep tp2 => type_beq tp1 tp2
  | T_Prod l1, T_Prod l2 => list_eqb type_beq l1 l2
  | T_Comb vn1 l1, T_Comb vn2 l2 => eqb vn1 vn2 && list_eqb type_beq l1 l2
  | T_Hole vn1, T_Hole vn2 => eqb vn1 vn2
  | _, _ => false
  end.

(* Функция поиска типа комбинации *)
Fixpoint type_comb_lookup 
      (Γ : type_context) 
      (ctor : type) 
      {struct Γ} : option (TypeName * type * list string * list type) :=
  match Γ with
  | [] => None
  | (BindCombType TN defctor holenames defargs) :: rest => 
      if type_beq ctor defctor then 
        Some (TN, defctor, holenames, defargs)
      else 
        type_comb_lookup rest ctor
  | _ :: rest => type_comb_lookup rest ctor
  end.

(* Вспомогательная функция для вывода типов для списка термов *)
Fixpoint infer_list 
          {A : Type} 
          (f : type_context -> A -> result type)
          (Γ : type_context)
          (ts : list A)
          {struct ts}
          : result (list type) :=
  match ts with
  | [] => Ok []
  | t :: rest =>
      match f Γ t with
      | Ok T =>
          match infer_list f Γ rest with
          | Ok Ts => Ok (T :: Ts)
          | Err e => Err e
          end
      | Err e => Err e
      end
  end.

Fixpoint comb_type_declared (ctx : type_context) (intn : TypeName) : bool :=
  match ctx with
  | [] => false
  | (BindCombType tn _ _ _) :: rest => 
      if eqb intn tn then 
        true
      else 
        comb_type_declared rest intn
  | _ :: rest => comb_type_declared rest intn
  end.

Definition type_abbr_declared (ctx : type_context) (intn : TypeName) : bool :=
  match type_abbr_lookup ctx intn with
  | Some _ => true
  | None => false
  end.

Fixpoint comb_type_closed (ctx : type_context) (intn : TypeName) : bool :=
  match ctx with
  | [] => false
  | (CloseCombType tn) :: rest => 
      if eqb intn tn then 
        true
      else 
        comb_type_closed rest intn
  | _ :: rest => comb_type_closed rest intn
  end.

Definition type_declared (ctx : type_context) (intn : TypeName) : bool :=
  comb_type_declared ctx intn || type_abbr_declared ctx intn.

(* Функция нормализации для типов *)
Fixpoint norm_type (Γ : type_context) (T : type) {struct T} : result type :=
    match T with
    | T_Abbr tn => 
        match type_abbr_lookup Γ tn with
        | Some T => Ok T
        | None => Err (Err_UnboundTypeAbbr tn)
        end
    | T_TRep ty => 
        match norm_type Γ ty with
        | Err e => Err e
        | Ok nrmty => Ok (T_TRep nrmty)
        end
    | T_Prod [x] => norm_type Γ x
    | T_Prod (p1 :: ps) =>
        match norm_list norm_type Γ (p1 :: ps) with 
        | Ok P => Ok (T_Prod P) 
        | Err e => Err e
        end
    | T_Comb tn typeparams => 
      match norm_list norm_type Γ typeparams with 
      | Ok nrmlst => Ok (T_Comb tn nrmlst) 
      | Err e => Err e
      end
    | _ => Ok T
    end.

Definition norm_type_beq
    (Γ : type_context)
    (T1 T2 : type) : result bool :=
  match norm_type Γ T1, norm_type Γ T2 with
  | Ok N1, Ok N2 => Ok (type_beq N1 N2)
  | Err e, _ => Err e
  | _, Err e => Err e
  end.

(* Функция булевого равенства для значений *)
Definition value_beq (fnteq : type -> type -> result bool) (fveq : value -> value -> bool) (it1 it2 : value) : result bool :=
  match it1, it2 with
  | V_Elem e1, V_Elem e2 => Ok (eqb e1 e2)
  | V_Prim p1, V_Prim p2 => Ok (prim_beq p1 p2)
  | V_TRep tp1, V_TRep tp2 => fnteq tp1 tp2
  | V_Prod l1, V_Prod l2 => Ok (list_eqb fveq l1 l2)
  | V_Comb ctor1 args1, V_Comb ctor2 args2 => 
      Ok (list_eqb fveq [ctor1] [ctor2] && list_eqb fveq args1 args2)
  | _, _ => Ok false
  end.

(* Подстановка типовых дыр. *)
Definition type_subst : Type :=
  list (string * type).

Fixpoint type_hole_lookup
    (subst : type_subst)
    (x : string)
  : option type :=
  match subst with
  | [] => None

  | (y, T) :: rest =>
      if eqb x y
      then Some T
      else type_hole_lookup rest x
  end.

(*
  Размер типа используется только для получения гарантированно
  достаточной глубины структурного обхода.

  Это не произвольный fuel: его значение вычисляется из самого типа.
*)
Fixpoint type_size (T : type) : nat :=
  match T with
  | T_Hole _ => 1
  | T_Abbr _ => 1
  | T_Elem _ => 1
  | T_Prim _ => 1

  | T_TRep T1 =>
      S (type_size T1)

  | T_Prod Ts =>
      S (fold_right
           (fun T n => type_size T + n)
           0
           Ts)

  | T_Comb _ Ts =>
      S (fold_right
           (fun T n => type_size T + n)
           0
           Ts)
  end.

(*
  Структурная унификация одного типа-шаблона с фактическим типом.

  ptrn: тип, который может содержать T_Hole.

  actual: фактический тип аргумента.

  Результат: расширенная подстановка типовых дыр.
*)
Fixpoint unify_type_fuel
    (fuel : nat)
    (subst : type_subst)
    (ptrn actual : type)
  : result type_subst :=

  match fuel with
  | 0 =>
      Err Err_InvalidType

  | S fuel' =>
      match ptrn with

      (* Унификация типовой дыры. *)
      | T_Hole x =>
          match type_hole_lookup subst x with

          (* Дыра уже была связана. *)
          | Some T =>
              if type_beq T actual
              then Ok subst
              else Err (Err_TypeMismatch T actual)

          (* Первое вхождение дыры. *)
          | None =>
              Ok ((x, actual) :: subst)
          end

      (* Аббревиатуры должны быть нормализованы заранее. *)
      | T_Abbr X =>
          match actual with
          | T_Abbr Y =>
              if eqb X Y
              then Ok subst
              else Err (Err_TypeMismatch ptrn actual)

          | _ =>
              Err (Err_TypeMismatch ptrn actual)
          end

      | T_Elem e1 =>
          match actual with
          | T_Elem e2 =>
              if eqb e1 e2
              then Ok subst
              else Err (Err_TypeMismatch ptrn actual)

          | _ =>
              Err (Err_TypeMismatch ptrn actual)
          end

      | T_Prim p1 =>
          match actual with
          | T_Prim p2 =>
              if prim_beq p1 p2
              then Ok subst
              else Err (Err_TypeMismatch ptrn actual)

          | _ =>
              Err (Err_TypeMismatch ptrn actual)
          end

      | T_TRep ptrn1 =>
          match actual with
          | T_TRep actual1 =>
              unify_type_fuel
                fuel'
                subst
                ptrn1
                actual1

          | _ =>
              Err (Err_TypeMismatch ptrn actual)
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
                  | [], [] =>
                      Ok subst0

                  | ptrn0 :: ptrn_rest,
                    actual0 :: actual_rest =>

                      match unify_type_fuel
                              fuel'
                              subst0
                              ptrn0
                              actual0
                      with
                      | Err e =>
                          Err e

                      | Ok subst1 =>
                          unify_product_elements
                            subst1
                            ptrn_rest
                            actual_rest
                      end

                  | _, _ =>
                      Err
                        (Err_TypeListMismatch
                           ptrns
                           actuals)
                  end

              in unify_product_elements
                   subst
                   ptrns
                   actuals

          | _ =>
              Err (Err_TypeMismatch ptrn actual)
          end

      | T_Comb ptrn_name ptrn_args =>
          match actual with
          | T_Comb actual_name actual_args =>

              if eqb ptrn_name actual_name
              then
                let fix unify_comb_arguments
                    (subst0 : type_subst)
                    (ptrns0 actuals0 : list type)
                    {struct ptrns0}
                    : result type_subst :=

                    match ptrns0, actuals0 with
                    | [], [] =>
                        Ok subst0

                    | ptrn0 :: ptrn_rest,
                      actual0 :: actual_rest =>

                        match unify_type_fuel
                                fuel'
                                subst0
                                ptrn0
                                actual0
                        with
                        | Err e =>
                            Err e

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

                in unify_comb_arguments
                     subst
                     ptrn_args
                     actual_args

              else
                Err (Err_TypeMismatch ptrn actual)

          | _ =>
              Err (Err_TypeMismatch ptrn actual)
          end
      end
  end.

Definition unify_type
    (subst : type_subst)
    (ptrn actual : type)
  : result type_subst :=
  unify_type_fuel
    (S (type_size ptrn))
    subst
    ptrn
    actual.

(*
  Унификация списка шаблонов со списком фактических типов.

  Подстановка передается от одного элемента к следующему,
  поэтому повторные вхождения одной дыры обязаны иметь
  одинаковый фактический тип.
*)
Fixpoint unify_type_list_aux
    (subst : type_subst)
    (ptrns actuals : list type)
    (original_ptrns original_actuals : list type)
    {struct ptrns}
  : result type_subst :=

  match ptrns, actuals with
  | [], [] =>
      Ok subst

  | ptrn :: ptrn_rest,
    actual :: actual_rest =>

      match unify_type subst ptrn actual with
      | Err e =>
          Err e

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

Definition unify_type_list (subst : type_subst) (ptrns actuals : list type)
  : result type_subst 
  := unify_type_list_aux subst ptrns actuals ptrns actuals.


(*
  Основной интерфейс унификации.

  Для совместимости с infer_comb_type_info функция по-прежнему
  возвращает список фактических типов.

  Внутри, однако, строится полноценная структурная подстановка.
*)
Definition unify_generic_list
    (plst arglst : list type)
  : result (list type) :=

  match unify_type_list
          []
          plst
          arglst
  with
  | Ok _ =>
      Ok arglst

  | Err e =>
      Err e
  end.

Definition infer_type_app (Γ : type_context) (t pt : type) : result type :=
  match t, pt with
  | T_Prod [], T_Prim _ => Err (TypeErr_InvalidApp t pt)
  | T_Prod (x :: xs), T_Prim Prm_Left => norm_type Γ x
  | T_Prod xs, T_Prim Prm_Right => norm_type Γ (last xs T_Unit)
  | _, _ => Err (TypeErr_InvalidApp t pt)
  end.

Fixpoint contains_hole (T : type) : bool :=
  match T with
  | T_Hole _ => true
  | T_TRep T => contains_hole T
  | T_Prod Ts => existsb contains_hole Ts
  | T_Comb _ Ts => existsb contains_hole Ts
  | _ => false
  end.

Fixpoint holenames_in_subst_lookup
    (holenames : list string)
    (subst : type_subst)
  : result (list type) :=
  match holenames with
  | [] => Ok []
  | str :: rest => 
      match holenames_in_subst_lookup rest subst with
      | Ok ts =>
          match type_hole_lookup subst str with
          | Some t => Ok (t :: ts) 
          | None => Err (Err_UnboundHole str)
          end
      | Err e => Err e
      end
  end.


(* Функция вывода и проверки типов *)
Fixpoint infer_type_expr (Γ : type_context) (tm : expr) {struct tm} : result type :=
  let infer_comb_type_decl_info Γ (ctor : expr) 
    : result (TypeName * type * list string * list type) :=
  match infer_type_expr Γ ctor with
  | Ok ctortype => 
      match type_comb_lookup Γ ctortype with
      | Some (tn, ctortype, holenames, argsptrn) => 
          Ok (tn, ctortype, holenames, argsptrn)
      | None => Err (Err_UnknownCombSignature)
      end
  | Err e => Err e
  end
  in
  let infer_comb_type_info Γ (ctor : expr) (arglst : list expr) 
    : result (TypeName * type * list type) :=
  match infer_comb_type_decl_info Γ ctor with
  | Ok (tn, ctortype, holenames, argsptrn) => 
      match infer_list infer_type_expr Γ arglst with
      | Ok argtypes =>
          match unify_type_list [] argsptrn argtypes with
          | Ok argsubst =>
              match holenames_in_subst_lookup holenames argsubst with
              | Ok typeargs =>
                   Ok (tn, ctortype, typeargs)
              | Err e => Err e
              end
          | Err e => Err e
          end
      | Err e => Err e
      end
  | Err e => Err e
  end
  in
  let infer_comb_prim_app (ctor : expr) (arglst : list expr) (prm : prim)
    : result type :=
  match infer_comb_type_info Γ ctor arglst with
  | Ok _ =>
      match infer_type_expr Γ ctor with
      | Ok ctortype => 
        match infer_list infer_type_expr Γ arglst with
        | Ok argtype =>
          match prm with
          | Prm_Left => norm_type Γ ctortype
          | Prm_Right => norm_type Γ (T_Prod argtype)
          end
        | Err e => Err e
        end
      | Err e => Err e
      end
  | Err e => Err e
  end
  in
  match tm with
  | E_Var x => 
      match var_type_lookup Γ x with
      | Some T => Ok T
      | None => Err (Err_UnboundVar x)
      end 
  | E_Elem u => Ok (T_Elem u)
  | E_Prim p => Ok (T_Prim p)
  | E_TRep T => 
      match norm_type Γ (T_TRep T) with
      | Ok nrmty => 
        if contains_hole nrmty then
          Err (Err_UseHoleInExpr tm)
        else
          Ok nrmty
      | Err e => Err e
      end
  | E_Prod [] => Ok T_Unit
  | E_Prod [x] => 
      match infer_type_expr Γ x with
      | Ok T => norm_type Γ T
      | Err e => Err e
      end
  | E_Prod (p1 :: ps) =>
      match infer_list infer_type_expr Γ (p1 :: ps) with
      | Ok P => norm_type Γ (T_Prod P)
      | Err e => Err e
      end
  | E_Comb ctor arglst => 
      match infer_comb_type_info Γ ctor arglst with
      | Ok (tn, _, typeargs) => 
          let trep_replace (t : type) : type :=
            match t with
            | T_TRep p => p
            | _ => t
            end
          in
            Ok (T_Comb tn (map trep_replace typeargs))
      | Err e => Err e
      end
  | E_App (E_Comb ctor arglst) (E_Prim prm) => 
      infer_comb_prim_app ctor arglst prm
  | E_App a b => 
    match infer_type_expr Γ a with
    | Err e => Err e
    | tares =>
      match infer_type_expr Γ b with
      | Err e => Err e
      | tbres =>
        match tares, tbres with
        | Ok ta, Ok tb => infer_type_app Γ ta tb
        | Err e, _ => Err e
        | Ok _, Err e => Err e
        end
      end
    end
  end.

(* Функция вычисления для выражений *) 
Fixpoint eval_expr (Sigma : eval_context) (tm : expr) {struct tm} : result value :=
  match tm with
  | E_Var x =>
      match var_value_lookup Sigma x with
      | Some v => Ok v
      | None => Err (Err_UnboundVar x)
      end
  | E_Elem e => Ok (V_Elem e)
  | E_Prim p => Ok (V_Prim p)
  | E_TRep T => 
      match norm_type [] T with
      | Ok TN => Ok (V_TRep TN)
      | Err e => Err e
      end
  | E_Prod p =>
      match p with
      | [] => Ok V_Unit
      | [x] => eval_expr Sigma x
      | _ =>
          match (eval_expr_list eval_expr Sigma p) with
          | Ok l => Ok (V_Prod l)
          | Err e => Err e
          end
      end
  | E_Comb inctor args =>
      match (eval_expr Sigma inctor) with
      | Ok ctor =>
          match (eval_expr_list eval_expr Sigma args) with
          | Ok a => Ok (V_Comb ctor a)
          | Err e => Err e
          end
      | Err e => Err e
      end
  | E_App a b =>
      match eval_expr Sigma a, eval_expr Sigma b with
      | Ok (V_Prod []), Ok (V_Prim _) => Err (ExprErr_InvalidApp a b)
      | Ok (V_Prod (x :: xs)), Ok (V_Prim Prm_Left) => Ok x
      | Ok (V_Prod xs), Ok (V_Prim Prm_Right) => Ok (last xs V_Unit)
      | Ok (V_Comb ctor _), Ok (V_Prim Prm_Left) => Ok ctor
      | Ok (V_Comb _ args), Ok (V_Prim Prm_Right) => 
        match args with
        | [] => Ok V_Unit
        | [x] => Ok x
        | xs => Ok (V_Prod xs)
        end
      | Ok _, Ok _ => Err (ExprErr_InvalidApp a b)
      | Err e, _ => Err e
      | Ok _, Err e => Err e 
      end
  end.

Definition exec_command (st : machine_state) (cmd : command) : result machine_state :=
  let Γ := ms_type_ctx st in
  let Sigma := ms_eval_ctx st in
  match cmd with
  | C_DeclVar x inex =>
      match var_value_lookup Sigma x, var_type_lookup Γ x with
      | None, None =>
          match infer_type_expr Γ inex with
          | Err e => Err e
          | tpres => 
              match tpres, eval_expr Sigma inex with
              | Ok t, Ok v => Ok {| 
                  ms_type_ctx := (BindVarType x t :: Γ);
                  ms_eval_ctx := (BindVarValue x v :: Sigma);
                  ms_last_type := ms_last_type st;
                  ms_last_value := ms_last_value st |}
              | Err er, _ => Err er
              | _, Err er => Err er
              end
          end
      | _, _ => Err (Err_DuplicateVar x)
      end
  | C_NewTypeAbbr x T => 
      match type_declared Γ x with
      | true => Err (Err_DuplicateType x)
      | false => 
        match norm_type Γ T with
        | Ok TN => Ok {| 
              ms_type_ctx := (BindTypeAbbr x TN :: Γ);
              ms_eval_ctx := Sigma;
              ms_last_type := ms_last_type st;
              ms_last_value := ms_last_value st |}
        | Err e => Err e
        end
      end
  | C_DeclCombVariant tn ctortype holenames args => 
      if comb_type_closed Γ tn then
        Err (Err_CombTypeClosed tn)
      else
      if type_abbr_declared Γ tn then
        Err (Err_DuplicateType tn)
      else
      match norm_type Γ ctortype with
      | Ok nrmctortype =>
        match type_comb_lookup Γ nrmctortype with
        | Some _ => Err (Err_DuplicateCombSignature tn nrmctortype)
        | None => 
            if contains_prim nrmctortype then
              Err (Err_UsePrimInDeclComb nrmctortype)
            else
            match norm_comb_list norm_type Γ args with
            | Ok nrmargs =>
                if contains_prim (T_Prod nrmargs) then
                  Err (Err_UsePrimInDeclComb (T_Prod nrmargs))
                else
                Ok {| 
                    ms_type_ctx := (BindCombType tn nrmctortype holenames nrmargs :: Γ);
                    ms_eval_ctx := Sigma;
                    ms_last_type := ms_last_type st;
                    ms_last_value := ms_last_value st |}
            | Err e => Err e
            end
        end
      | Err e => Err e
      end
  | C_Eval e =>
      match infer_type_expr Γ e with
      | Err er => Err er
      | tres =>
          match eval_expr Sigma e with
          | Err er => Err er
          | eres =>
            match tres, eres with
            | Ok T, Ok v => Ok {| 
                ms_type_ctx := Γ;
                ms_eval_ctx := Sigma;
                ms_last_type := T;
                ms_last_value := v |}
            | Err er, _ => Err er
            | _, Err er => Err er
            end
          end
      end
  | C_CloseCombType tn => 
      if negb (comb_type_declared Γ tn) then
        Err (Err_CloseUnknownCombType tn)
      else if comb_type_closed Γ tn then 
        Err (Err_CombTypeAlreadyClosed tn)
      else
        Ok {| 
          ms_type_ctx := (CloseCombType tn :: Γ);
          ms_eval_ctx := Sigma;
          ms_last_type := ms_last_type st;
          ms_last_value := ms_last_value st |}
  end.

Definition prog : Type := list command.

(*
  Окружение уже раскрытых определений типов.
  В отличие от type_context, здесь хранятся именно определения имён типов.
*)
Definition type_def_context : Type :=
  list (TypeName * type).

(* Окружение уже раскрытых определений термов. *)
Definition expr_def_context : Type :=
  list (VarName * expr).

Fixpoint lookup_type_def
    (Delta : type_def_context)
    (X : TypeName)
  : option type :=
  match Delta with
  | [] => None
  | (Y, T) :: rest =>
      if eqb X Y
      then Some T
      else lookup_type_def rest X
  end.

Fixpoint lookup_expr_def
    (Sigma : expr_def_context)
    (x : VarName)
  : option expr :=
  match Sigma with
  | [] => None
  | (y, tm) :: rest =>
      if eqb x y
      then Some tm
      else lookup_expr_def rest x
  end.

Fixpoint unfold_list
          {A : Type} 
          (f : expr_def_context -> type_def_context -> A -> result A)
          (Sigma : expr_def_context)
          (Delta : type_def_context)
          (xs : list A) 
          : result (list A) :=
  match xs with
  | [] => Ok []
  | x :: rest =>
     match f Sigma Delta x with
     | Ok xn =>
        match unfold_list f Sigma Delta rest with
        | Ok newrest => Ok (xn :: newrest)
        | Err e => Err e
        end
     | Err e => Err e
     end
  end.

Fixpoint unfold_type
    (Sigma : expr_def_context)
    (Delta : type_def_context)
    (T : type) {struct T}
  : result type :=
  match T with
  | T_Abbr X =>
      match lookup_type_def Delta X with
      | Some T' => Ok T'
      | None => Err (Err_UnboundTypeAbbr X)
      end
  | T_Hole vn => Ok (T_Hole vn)
  | T_Elem e => Ok (T_Elem e)
  | T_Prim p => Ok (T_Prim p)

  | T_TRep T1 => 
      match unfold_type Sigma Delta T1 with
      | Ok TN => Ok (T_TRep TN)
      | Err e => Err e
      end

  | T_Prod Ts =>
        match unfold_list unfold_type Sigma Delta Ts with
        | Ok newts => Ok (T_Prod newts)
        | Err e => Err e
        end
  | T_Comb tn lst => 
      match unfold_list unfold_type Sigma Delta lst with
      | Ok newlst => Ok (T_Comb tn newlst)
      | Err e => Err e
      end
  end.

Fixpoint unfold_expr
    (Sigma : expr_def_context)
    (Delta : type_def_context)
    (tm : expr) {struct tm}
  : result expr :=
  match tm with
  | E_Var x =>
      match lookup_expr_def Sigma x with
      | Some tm' => Ok tm'
      | None => Err (Err_UnboundVar x)
      end
      
  | E_Elem e => Ok (E_Elem e)
  | E_Prim p => Ok (E_Prim p)

  | E_TRep T =>
      match unfold_type Sigma Delta T with
      | Ok TN => Ok (E_TRep TN)
      | Err e => Err e
      end

  | E_Prod ts =>
        match unfold_list unfold_expr Sigma Delta ts with
        | Ok newts => Ok (E_Prod newts)
        | Err e => Err e
        end
  
  | E_Comb ctor args => 
      match unfold_expr Sigma Delta ctor with
      | Ok newctor => 
          match unfold_list unfold_expr Sigma Delta args with
          | Ok newargs => Ok (E_Comb newctor newargs)
          | Err e => Err e
          end
      | Err e => Err e
      end
  | E_App a b =>
    match unfold_expr Sigma Delta a with
    | Ok x => 
        match unfold_expr Sigma Delta b with
        | Ok y => Ok (E_App x y)
        | Err e => Err e
        end
    | Err e => Err e
    end
  end.

Fixpoint unfold_prog_aux
    (Sigma : expr_def_context)
    (Delta : type_def_context)
    (prg : prog) {struct prg}
  : result prog :=
  match prg with
  | [] => Ok []

  | C_DeclVar x rhs :: rest =>
      match unfold_expr Sigma Delta rhs with
      | Ok rhs' => 
          match unfold_prog_aux ((x, rhs') :: Sigma) Delta rest with
          | Ok restprg => Ok (C_DeclVar x rhs' :: restprg)
          | Err e => Err e
          end
      | Err e => Err e
      end

  | C_NewTypeAbbr X T :: rest =>
      match unfold_type Sigma Delta T with
      | Ok T' => 
          match unfold_prog_aux Sigma ((X, T') :: Delta) rest with
          | Ok restprg => Ok (C_NewTypeAbbr X T' :: restprg)
          | Err e => Err e
          end
      | Err e => Err e
      end

  | C_DeclCombVariant tn ctor holenames args :: rest =>
      match unfold_type Sigma Delta ctor with
      | Err e => Err e
      | Ok newctor =>
          match unfold_type Sigma Delta (T_Prod args) with
          | Err e => Err e
          | Ok (T_Prod newargs) => 
            match unfold_prog_aux Sigma Delta rest with
            | Ok restprg => Ok (C_DeclCombVariant tn newctor holenames newargs :: restprg)
            | Err e => Err e
            end
          | Ok _ => Err Err_InvalidType
          end
      end

  | C_Eval e :: rest => 
      match unfold_expr Sigma Delta e with
      | Ok e' =>
          match unfold_prog_aux Sigma Delta rest with
          | Ok restprg => Ok (C_Eval e' :: restprg)
          | Err er => Err er
          end
      | Err er => Err er
      end
      
  | C_CloseCombType tn :: rest =>
      match unfold_prog_aux Sigma Delta rest with
      | Ok restprg => Ok (C_CloseCombType tn :: restprg)
      | Err er => Err er
      end
  end.

Definition unfold_prog (prg : prog) : result prog :=
  unfold_prog_aux [] [] prg.

Record Prg_Result := {prog_type : type; prog_val : value}.

Fixpoint compile_prog_aux (st : machine_state) (prg : prog) {struct prg} : result machine_state :=
  match prg with
  | [] => Ok st
  | c :: rest =>
      match exec_command st c with
      | Ok st' => compile_prog_aux st' rest
      | Err e => Err e
      end
  end.

Definition compile_prog (inprg : prog) : result Prg_Result :=
  match unfold_prog inprg with
  | Ok newprg => 
      match compile_prog_aux initial_state newprg with
      | Ok st => Ok {| prog_type := ms_last_type st; prog_val := ms_last_value st |}
      | Err e => Err e
      end
  | Err e => Err e
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


