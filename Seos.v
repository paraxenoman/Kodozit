(* Kodozit.Seos Formal Theory @ Paraxenoman *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Definition TypeName : Type := string.
Definition VarName : Type := string.
Definition elem : Type := string.

Inductive prim : Type := (* TODO *).

(* Синтаксис типов  *)
Inductive type : Type :=
  | Ty_Var : TypeName -> type
  | Ty_ReadyVar : type
  | Ty_Elem : elem -> type
  | Ty_Prim : prim -> type
  | Ty_Sing : term -> type
  | Ty_Subst : type -> type
  | Ty_Prod : list type -> type
with term : Type :=
(* Синтаксис термов  *)
  | Tm_Var : VarName -> term
  | Tm_DeclVar : VarName -> term -> term
  | Tm_ReadyVar : term
  | Tm_Elem : elem -> term
  | Tm_Prim : prim -> term
  | Tm_Sing : term -> term
  | Tm_Subst : type -> term
  | Tm_Prod : list term -> term.

Notation Tm_Unit := (Tm_Prod []).
Notation Ty_Unit := (Ty_Prod []).

Inductive TypeBinding : Type :=
  | BindTypeName : TypeName -> type -> TypeBinding
  | BindVarType : VarName -> type -> TypeBinding
  | BindCombType : list type -> type -> TypeBinding.

(* Контекст типизации *)
Definition type_context := list TypeBinding.

Fixpoint type_name_lookup (Gamma : type_context) (X : TypeName) : option type :=
  match Gamma with
  | [] => None
  | (BindTypeName Y T) :: rest => if eqb X Y then Some T else type_name_lookup rest X
  | _ :: rest => type_name_lookup rest X
  end.

(* Функция поиска типа переменной в контексте *)
Fixpoint var_type_lookup (Gamma : type_context) (x : VarName) : option type :=
  match Gamma with
  | [] => None
  | (BindVarType y T) :: rest => if eqb x y then Some T else var_type_lookup rest x
  | _ :: rest => var_type_lookup rest x
  end.

(* Отношение типизации (Gamma |- t : T) *) 

Reserved Notation "Γ '⊢' t '∈' A" (at level 40, t at level 99, A at level 60).

Inductive has_type : type_context -> term -> type -> Prop :=
  | ht_var : forall Γ x T,
      var_type_lookup Γ x = Some T ->
      type_wf Γ T ->
      Γ ⊢ (Tm_Var x) ∈ T
      
  | ht_decl_var : forall Γ x v T,
      var_type_lookup Γ x = None ->
      Γ ⊢ v ∈ T ->
      T <> Ty_ReadyVar ->
      type_wf Γ T ->
      Γ ⊢ (Tm_DeclVar x v) ∈ Ty_ReadyVar

  | ht_elem : forall Γ u, 
        Γ ⊢ (Tm_Elem u) ∈ (Ty_Elem u)
  | ht_prim : forall Γ p, 
        Γ ⊢ (Tm_Prim p) ∈ (Ty_Prim p)

  | ht_unit : forall Γ,
      Γ ⊢ Tm_Unit ∈ Ty_Unit
  
  | ht_prod_mono : forall Γ x T,
      type_wf Γ T ->
      Γ ⊢ x ∈ T ->
      T <> Ty_ReadyVar ->
      Γ ⊢ (Tm_Prod [x]) ∈ T
  
  | ht_sing : forall Γ s S,
      type_wf Γ S ->
      Γ ⊢ s ∈ S ->
      S <> Ty_ReadyVar ->
      Γ ⊢ (Tm_Sing s) ∈ (Ty_Sing s)

  | ht_subst : forall Γ T,
      type_wf Γ T ->
      T <> Ty_ReadyVar ->
      Γ ⊢ (Tm_Subst T) ∈ (Ty_Subst T)

  | ht_prod : forall Γ p P x,
      p <> [] ->
      p <> [x] ->
      Forall2 (fun v V => 
        (type_wf Γ V /\ V <> Ty_ReadyVar /\ Γ ⊢ v ∈ V)
      ) p P ->
      Γ ⊢ (Tm_Prod p) ∈ (Ty_Prod P)
(* Отношение well-formedness для типов *)
with type_wf : type_context -> type -> Prop :=
  | wf_var : forall Γ X T,
      type_name_lookup Γ X = Some T ->
      type_wf Γ T ->
      T <> Ty_ReadyVar ->
      type_wf Γ (Ty_Var X)
  | wf_readyvar : forall Γ, type_wf Γ Ty_ReadyVar
  | wf_unit : forall Γ, type_wf Γ Ty_Unit

  | wf_elem : forall Γ u, 
      type_wf Γ (Ty_Elem u)

  | wf_prim : forall Γ p, 
      type_wf Γ (Ty_Prim p)

  | wf_sing : forall Γ s S, 
      has_type Γ s S ->
      S <> Ty_ReadyVar ->
      type_wf Γ (Ty_Sing s)

  | wf_subst : forall Γ T, 
      type_wf Γ T ->
      T <> Ty_ReadyVar ->
      type_wf Γ (Ty_Subst T)

  | wf_prod_mono : forall Γ X,
      type_wf Γ X ->
      X <> Ty_ReadyVar ->
      type_wf Γ (Ty_Prod [X])

  | wf_prod : forall Γ P X, 
      P <> [] ->
      P <> [X] ->
      Forall (fun t => type_wf Γ t /\ t <> Ty_ReadyVar) P ->
      type_wf Γ (Ty_Prod P)

where "Γ '⊢' t '∈' A" := (has_type Γ t A).

Inductive InferTypeResult : Type :=
  | TypeCtx : (option type) -> type_context -> InferTypeResult.
  
Definition sometype t Gamma := TypeCtx (Some t) Gamma.
Definition notype Gamma := TypeCtx None Gamma.

(* Функция вывода и проверки типов *)
Fixpoint infer_type_term (Gamma : type_context) (tm : term) : InferTypeResult :=
  match tm with
    | Tm_Var x => TypeCtx (var_type_lookup Gamma x) Gamma
    | Tm_DeclVar x tm =>
        match var_type_lookup Gamma x with
        | Some _ => notype Gamma
        | None =>
            match infer_type_term Gamma tm with
            | TypeCtx None _ => notype Gamma
            | TypeCtx (Some T) Gamma1 => 
                match T with
                | Ty_ReadyVar => notype Gamma
                | _ => sometype Ty_ReadyVar (BindVarType x T :: Gamma1)
                end
            end
        end
    | Tm_ReadyVar => sometype Ty_ReadyVar Gamma
    | Tm_Elem u => sometype (Ty_Elem u) Gamma
    | Tm_Prim p => sometype (Ty_Prim p) Gamma
    | Tm_Sing s =>
        match infer_type_term Gamma s with
        | TypeCtx (Some T) _ => 
            match T with
            | Ty_ReadyVar => notype Gamma
            | _ => sometype (Ty_Sing s) Gamma
            end
        | TypeCtx None _ => notype Gamma
        end
    | Tm_Subst T => 
        match T with
        | Ty_ReadyVar => notype Gamma
        | _ => sometype (Ty_Subst T) Gamma (* TODO Обеспечить wf T *)
        end
    | Tm_Prod [] => sometype Ty_Unit Gamma
    | Tm_Prod [x] => 
        match infer_type_term Gamma x with
        | TypeCtx (Some T) _ => 
            match T with
            | Ty_ReadyVar => notype Gamma
            | _ => sometype T Gamma
            end
        | _ => notype Gamma
        end
    | Tm_Prod (p1 :: ps) =>
        let fix infer_list (ts : list term) : option (list type) :=
          match ts with
          | [] => Some []
          | t :: rest =>
              match infer_type_term Gamma t with
              | TypeCtx (Some T) _ =>
                  match T with
                  | Ty_ReadyVar => None
                  | _ => 
                      match infer_list rest with
                      | Some Ts => Some (T :: Ts)
                      | None => None
                      end
                  end
              | TypeCtx None _ => None
              end
          end
        in
        TypeCtx (match infer_list (p1 :: ps) with Some P => Some (Ty_Prod P) | None => None end) Gamma
    end.

Inductive VarValueBinding : Type :=
  | BindVarValue : VarName -> term -> VarValueBinding.

(* Контекст вычислений *)
Definition eval_context := list VarValueBinding.

(* Функция поиска значения переменной в контексте вычислений *)
Fixpoint var_value_lookup (Sigma : eval_context) (x : VarName) : option term :=
  match Sigma with
  | [] => None
  | (BindVarValue y v1) :: rest => if eqb x y then Some v1 else var_value_lookup rest x
  end.

(* Индуктивное отношение принадлежности терма нормальной форме *) 
Inductive is_value : term -> Prop := 
  | val_readyvar : is_value Tm_ReadyVar
  | val_elem : forall e,
      is_value (Tm_Elem e)

  | val_prim : forall p,
      is_value (Tm_Prim p)

  | val_sing : forall t,
      is_value t ->
      is_value (Tm_Sing t)

  | val_subst : forall T,
      is_value (Tm_Subst T)

  | val_unit : is_value Tm_Unit

  | val_prod : forall p x,
      p <> [] ->
      p <> [x] ->
      Forall (fun v => is_value v) p ->
      is_value (Tm_Prod p).

(* Индуктивное отношение вычисления малого шага *) 
Inductive step : eval_context -> term -> term -> eval_context -> Prop := 
  | st_var : forall Sigma n v,
      var_value_lookup Sigma n = Some v -> 
      step Sigma (Tm_Var n) v Sigma
  
  | st_declvar : forall Sigma x t v,
      step Sigma t v Sigma ->
      v <> Tm_ReadyVar ->
      step Sigma (Tm_DeclVar x t) Tm_ReadyVar (BindVarValue x v:: Sigma)
  
  | st_sing : forall Sigma t v,
      step Sigma t v Sigma ->
      v <> Tm_ReadyVar ->
      step Sigma (Tm_Sing t) (Tm_Sing v) Sigma
  
  | st_prod_mono : forall Sigma x v,
      step Sigma x v Sigma ->
      v <> Tm_ReadyVar ->
      step Sigma (Tm_Prod (x :: [])) v Sigma

  | st_prod : forall Sigma p1 p2,
      p1 <> [] ->
      Forall2 (fun v1 v2 => step Sigma v1 v2 Sigma 
                  /\ v2 <> Tm_ReadyVar) p1 p2 ->
      step Sigma (Tm_Prod p1) (Tm_Prod p2) Sigma.

Inductive EvalResult : Type :=
  | ValCtx : option term -> eval_context -> EvalResult.
  
Definition somevalue term Sigma := ValCtx (Some term) Sigma.
Definition novalue Sigma := ValCtx None Sigma.

(* Функция вычисления термов *)
Fixpoint eval_term (Sigma : eval_context) (tm : term) : EvalResult :=
  match tm with
  | Tm_Var x =>
      match var_value_lookup Sigma x with
      | Some v => somevalue v Sigma
      | None => novalue Sigma
      end
  | Tm_DeclVar x v =>
      match var_value_lookup Sigma x with
      | Some _ => novalue Sigma
      | None => 
          match eval_term Sigma v with
          | ValCtx (Some Tm_ReadyVar) _ => novalue Sigma
          | ValCtx (Some v1) Sigma1 => somevalue Tm_ReadyVar (BindVarValue x v1 :: Sigma1)
          | _ => novalue Sigma
          end
      end
  | Tm_ReadyVar => somevalue Tm_ReadyVar Sigma 
  | Tm_Elem e => somevalue (Tm_Elem e) Sigma
  | Tm_Prim p => somevalue (Tm_Prim p) Sigma
  | Tm_Sing s =>
      match eval_term Sigma s with
      | ValCtx (Some Tm_ReadyVar) _ => novalue Sigma
      | ValCtx (Some v) _ => somevalue (Tm_Sing v) Sigma
      | _ => novalue Sigma
      end
  | Tm_Subst Ty_ReadyVar => novalue Sigma
  | Tm_Subst T => somevalue (Tm_Subst T) Sigma
  | Tm_Prod p =>
      match p with
      | [] => somevalue Tm_Unit Sigma
      | [x] => 
          match eval_term Sigma x with
          | ValCtx (Some Tm_ReadyVar) _ => novalue Sigma
          | v => v
          end
      | _ =>
          let fix eval_list (ts : list term) : option (list term) :=
            match ts with
            | [] => Some []
            | t :: rest =>
                match eval_term Sigma t with
                | ValCtx (Some Tm_ReadyVar) _ => None
                | ValCtx (Some v) _ => 
                    match (eval_list rest) with
                    | Some lt => Some (v :: lt)
                    | _ => None
                    end
                | _ => None
                end
            end
          in
          match (eval_list p) with
          | Some l => somevalue (Tm_Prod l) Sigma
          | _ => novalue Sigma
          end
      end
  end.

Definition prog : Type := list term.

(* Вспомогательная функция для последовательного вывода типов для списка термов (программы)
   с протаскиванием обновленного контекста типизации *)
Fixpoint infer_type_prog (Gamma : type_context) (prg : prog) : InferTypeResult :=
  match prg with
  | [] => TypeCtx (Some Ty_Unit) Gamma
  | [t] => infer_type_term Gamma t
  | t :: rest =>
      match infer_type_term Gamma t with
      | TypeCtx (Some _) Gamma1 => infer_type_prog Gamma1 rest
      | TypeCtx None Gamma1 => notype Gamma1
      end
  end.

(* Основная функция проверки типа программы, возвращающая option type *)
Definition infer (ctx : type_context) (prg : prog) : option type :=
  match infer_type_prog ctx prg with
  | TypeCtx opt_t _ => opt_t
  end.

(* Вспомогательная функция для последовательного вычисления списка термов (программы)
   с протаскиванием обновленного контекста вычислений (eval_context). *)
Fixpoint eval_prog (Sigma : eval_context) (prg : prog) : EvalResult :=
  match prg with
  | [] => ValCtx (Some Tm_Unit) Sigma
  | [t] => eval_term Sigma t
  | t :: rest =>
      match eval_term Sigma t with
      | ValCtx (Some _) Sigma1 => eval_prog Sigma1 rest
      | ValCtx None Sigma1 => novalue Sigma1
      end
  end.

(* Основная функция вычисления программы, возвращающая option term *)
Definition eval (ctx : eval_context) (prg : prog) : option term :=
  match eval_prog ctx prg with
  | ValCtx opt_v _ => opt_v
  end.


(* Тривиальный пример хорошей программы *)
Definition example_good_prog := [Tm_DeclVar "input" (Tm_Elem "bla"); Tm_DeclVar "myvar" (Tm_Prod [Tm_Elem "0"; Tm_Var "input"; Tm_Elem "2"; Tm_Elem "VAL"]); Tm_Var "myvar"].
Compute (eval_prog [] example_good_prog).
Compute (infer [] example_good_prog).

(* Тривиальный пример плохой программы - undefined variable bad *)
Definition example_bad_prog := (Tm_DeclVar "bed" (Tm_Elem "()") :: Tm_Var "bad" :: []).
Compute (eval_prog [] example_bad_prog).
Compute (infer [] example_bad_prog).

(* Ещё пример плохой программы - объявление переменных не на топлевеле *)
Definition example_bad_prog2 := [Tm_Prod [Tm_Elem ""; Tm_DeclVar "bed" (Tm_Elem "()")]].
Compute (eval_prog [] example_bad_prog2).
Compute (infer [] example_bad_prog2).

(* Ещё пример плохой программы - затенение переменных *)
Definition example_bad_prog3 := [Tm_DeclVar "input" (Tm_Elem "bla"); Tm_DeclVar "input" (Tm_Prod [Tm_Elem "0"; Tm_Elem "2"; Tm_Elem "VAL"]); Tm_Var "myvar"].
Compute (eval_prog [] example_bad_prog3).
Compute (infer [] example_bad_prog3).

(* Ещё пример плохой программы - прямое использование Ty_ReadyVar *)
Definition example_bad_prog4 := [Tm_Subst Ty_ReadyVar].
Compute (eval_prog [] example_bad_prog4).
Compute (infer [] example_bad_prog4).
