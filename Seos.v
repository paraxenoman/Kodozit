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

Inductive InferTypeResult : Type :=
  | TypeCtx : type -> type_context -> InferTypeResult
  | FailType : InferTypeResult.

Definition sometype t Γ := TypeCtx t Γ.
Definition notype := FailType.

Fixpoint type_name_lookup (Γ : type_context) (X : TypeName) : InferTypeResult :=
  match Γ with
  | [] => FailType
  | (BindTypeName Y T) :: rest => if eqb X Y then sometype T Γ else type_name_lookup rest X
  | _ :: rest => type_name_lookup rest X
  end.

(* Функция поиска типа переменной в контексте *)
Fixpoint var_type_lookup (Γ : type_context) (x : VarName) : InferTypeResult :=
  match Γ with
  | [] => FailType
  | (BindVarType y T) :: rest => if eqb x y then sometype T Γ else var_type_lookup rest x
  | _ :: rest => var_type_lookup rest x
  end.

(* Отношение типизации (Γ ⊢ t ∈ A) *) 

Reserved Notation "Γ '⊢' t '∈' A" (at level 40, t at level 99, A at level 60).

Inductive has_type : type_context -> term -> type -> Prop :=
  | ht_var : forall Γ x T X,
      var_type_lookup Γ x = TypeCtx T Γ ->
      norm_wf_type Γ T X ->
      Γ ⊢ (Tm_Var x) ∈ X

  | ht_decl_var : forall Γ x v T X,
      var_type_lookup Γ x = FailType ->
      Γ ⊢ v ∈ T ->
      norm_wf_type Γ T X ->
      (BindVarType x X :: Γ) ⊢ (Tm_DeclVar x v) ∈ Ty_ReadyVar

  | ht_decl_var_upd : forall Γ x v X,
      (BindVarType x X :: Γ) ⊢ (Tm_DeclVar x v) ∈ Ty_ReadyVar ->
      (BindVarType x X :: Γ) ⊢ (Tm_Var x) ∈ X

  | ht_readyvar : forall Γ, Γ ⊢ Tm_ReadyVar ∈ Ty_ReadyVar

  | ht_elem : forall Γ u, 
        Γ ⊢ (Tm_Elem u) ∈ (Ty_Elem u)
  | ht_prim : forall Γ p, 
        Γ ⊢ (Tm_Prim p) ∈ (Ty_Prim p)

  | ht_unit : forall Γ,
      Γ ⊢ Tm_Unit ∈ Ty_Unit

  | ht_prod_mono : forall Γ x T X,
      norm_wf_type Γ T X ->
      Γ ⊢ x ∈ X ->
      Γ ⊢ (Tm_Prod [x]) ∈ X

  | ht_sing : forall Γ s S X,
      norm_wf_type Γ S X ->
      Γ ⊢ s ∈ X ->
      Γ ⊢ (Tm_Sing s) ∈ (Ty_Sing s)

  | ht_subst : forall Γ T X,
      norm_wf_type Γ T X ->
      Γ ⊢ (Tm_Subst T) ∈ (Ty_Subst X)
 
  | ht_prod : forall Γ p P x,
      p <> [] ->
      p <> [x] ->
      Forall2 (has_type Γ) p P ->
      Γ ⊢ (Tm_Prod p) ∈ (Ty_Prod P)
(* Отношение нормализации и well-formedness для типов *)
with norm_wf_type : type_context -> type -> type -> Prop :=
    
    | nwft_var : forall Γ t T X y,
      type_name_lookup Γ t = TypeCtx T Γ ->
      norm_wf_type Γ T X ->
      X <> Ty_ReadyVar ->
      X <> (Ty_Var y) ->
      norm_wf_type Γ (Ty_Var t) X
      
    | nwft_readyvar : forall Γ, norm_wf_type Γ Ty_ReadyVar Ty_ReadyVar
    
    | nwft_unit : forall Γ, norm_wf_type Γ Ty_Unit Ty_Unit
    
    | nwft_elem : forall Γ e, norm_wf_type Γ (Ty_Elem e) (Ty_Elem e)
    
    | nwft_prim : forall Γ p, norm_wf_type Γ (Ty_Prim p) (Ty_Prim p)
    
    | nwft_sing : forall Γ s S X y, 
        Γ ⊢ s ∈ S ->
        norm_wf_type Γ S X ->
        X <> Ty_ReadyVar ->
        X <> (Ty_Var y) ->
        norm_wf_type Γ (Ty_Sing s) (Ty_Sing s)
    
    | nwft_subst : forall Γ T X y,
        norm_wf_type Γ T X ->
        X <> Ty_ReadyVar ->
        X <> (Ty_Var y) ->
        norm_wf_type Γ (Ty_Subst T) (Ty_Subst X)
    
    | nwft_prod_mono : forall Γ T X y,
        norm_wf_type Γ T X ->
        X <> Ty_ReadyVar ->
        X <> (Ty_Var y) ->
        norm_wf_type Γ (Ty_Prod [T]) X

    | nwft_prod : forall Γ P X P2 y, 
        P <> [] ->
        P <> [X] ->
        Forall2 (fun t t2 => 
                    norm_wf_type Γ t t2 /\ t2 <> Ty_ReadyVar /\ t2 <> (Ty_Var y)) P P2 ->
        norm_wf_type Γ (Ty_Prod P) (Ty_Prod P2)
where "Γ '⊢' t '∈' A" := (has_type Γ t A).

(* Функция вывода и проверки типов *)
Fixpoint infer_type_term (Γ : type_context) (tm : term) : InferTypeResult :=
  match tm with
    | Tm_Var x => var_type_lookup Γ x
    | Tm_DeclVar x tm =>
        match var_type_lookup Γ x with
        | TypeCtx _ _ => notype
        | FailType =>
            match infer_type_term Γ tm with
            | FailType => notype
            | TypeCtx T Γ2 => 
                match T with
                | Ty_ReadyVar => notype
                | _ => sometype Ty_ReadyVar (BindVarType x T :: Γ2)
                end
            end
        end
    | Tm_ReadyVar => sometype Ty_ReadyVar Γ
    | Tm_Elem u => sometype (Ty_Elem u) Γ
    | Tm_Prim p => sometype (Ty_Prim p) Γ
    | Tm_Sing s =>
        match infer_type_term Γ s with
        | TypeCtx T _ => 
            match T with
            | Ty_ReadyVar => notype
            | _ => sometype (Ty_Sing s) Γ
            end
        | FailType => notype
        end
    | Tm_Subst T => 
        match T with
        | Ty_ReadyVar => notype
        | _ => sometype (Ty_Subst T) Γ (* TODO Обеспечить wf T *)
        end
    | Tm_Prod [] => sometype Ty_Unit Γ
    | Tm_Prod [x] => 
        match infer_type_term Γ x with
        | TypeCtx T _ => 
            match T with
            | Ty_ReadyVar => notype
            | _ => sometype T Γ
            end
        | FailType => notype
        end
    | Tm_Prod (p1 :: ps) =>
        let fix infer_list (ts : list term) : option (list type) :=
          match ts with
          | [] => Some []
          | t :: rest =>
              match infer_type_term Γ t with
              | TypeCtx T _ =>
                  match T with
                  | Ty_ReadyVar => None
                  | _ => 
                      match infer_list rest with
                      | Some Ts => Some (T :: Ts)
                      | None => None
                      end
                  end
              | FailType => None
              end
          end
        in
        match infer_list (p1 :: ps) with Some P => sometype (Ty_Prod P) Γ | None => FailType end
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
  | ValCtx : term -> eval_context -> EvalResult
  | FailValue : EvalResult.
  
Definition somevalue term Sigma := ValCtx term Sigma.
Definition novalue := FailValue.

(* Функция вычисления термов *)
Fixpoint eval_term (Sigma : eval_context) (tm : term) : EvalResult :=
  match tm with
  | Tm_Var x =>
      match var_value_lookup Sigma x with
      | Some v => somevalue v Sigma
      | None => novalue
      end
  | Tm_DeclVar x v =>
      match var_value_lookup Sigma x with
      | Some _ => novalue
      | None => 
          match eval_term Sigma v with
          | ValCtx Tm_ReadyVar _ => novalue
          | ValCtx v1 Sigma1 => somevalue Tm_ReadyVar (BindVarValue x v1 :: Sigma1)
          | FailValue => novalue
          end
      end
  | Tm_ReadyVar => somevalue Tm_ReadyVar Sigma 
  | Tm_Elem e => somevalue (Tm_Elem e) Sigma
  | Tm_Prim p => somevalue (Tm_Prim p) Sigma
  | Tm_Sing s =>
      match eval_term Sigma s with
      | ValCtx Tm_ReadyVar _ => novalue
      | ValCtx v _ => somevalue (Tm_Sing v) Sigma
      | FailValue => novalue
      end
  | Tm_Subst Ty_ReadyVar => novalue
  | Tm_Subst T => somevalue (Tm_Subst T) Sigma
  | Tm_Prod p =>
      match p with
      | [] => somevalue Tm_Unit Sigma
      | [x] => 
          match eval_term Sigma x with
          | ValCtx Tm_ReadyVar _ => novalue
          | v => v
          end
      | _ =>
          let fix eval_list (ts : list term) : option (list term) :=
            match ts with
            | [] => Some []
            | t :: rest =>
                match eval_term Sigma t with
                | ValCtx Tm_ReadyVar _ => None
                | ValCtx v _ => 
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
          | _ => novalue
          end
      end
  end.

Definition prog : Type := list term.

(* Основная функция проверки типа программы *)
Fixpoint infer_type_prog (Γ : type_context) (prg : prog) : option type :=
  let fix f g p {struct p} := match p with
  | [] => TypeCtx Ty_Unit g
  | [t] => infer_type_term g t
  | t :: rest =>
      match infer_type_term g t with
      | TypeCtx _ Γ2 =>
           match infer_type_prog Γ2 rest with
           | Some tp => TypeCtx tp Γ2
           | None => FailType
           end
      | FailType => notype
      end
  end
  in
  match f Γ prg with
  | TypeCtx t _ => Some t
  | _ => None
  end.

(* Основная функция вычисления программы *)
Fixpoint eval_prog (Sigma : eval_context) (prg : prog) : option term :=
  let fix f s p := match prg with
  | [] => ValCtx Tm_Unit s
  | [t] => eval_term s t
  | t :: rest =>
      match eval_term s t with
      | ValCtx _ s1 => 
          match eval_prog s1 rest with
          | Some tm => ValCtx tm s1
          | None => FailValue
          end
      | FailValue => novalue
      end
  end
  in
  match f Sigma prg with
  | ValCtx t _ => Some t
  | _ => None
  end.


(* Тривиальный пример хорошей программы *)
Example example_good_prog := [Tm_DeclVar "input" (Tm_Elem "bla"); Tm_DeclVar "myvar" (Tm_Prod [Tm_Elem "0"; Tm_Var "input"; Tm_Elem "2"; Tm_Elem "VAL"]); Tm_Var "myvar"].
Compute (eval_prog [] example_good_prog).
Compute (infer_type_prog [] example_good_prog).

(* Тривиальный пример плохой программы - undefined variable bad *)
Example example_bad_prog := (Tm_DeclVar "bed" (Tm_Elem "()") :: Tm_Var "bad" :: []).
Compute (eval_prog [] example_bad_prog).
Compute (infer_type_prog [] example_bad_prog).

(* Ещё пример плохой программы - объявление переменных не на топлевеле *)
Example example_bad_prog2 := [Tm_Prod [Tm_Elem ""; Tm_DeclVar "bed" (Tm_Elem "()")]].
Compute (eval_prog [] example_bad_prog2).
Compute (infer_type_prog [] example_bad_prog2).

(* Ещё пример плохой программы - затенение переменных *)
Example example_bad_prog3 := [Tm_DeclVar "input" (Tm_Elem "bla"); Tm_DeclVar "input" (Tm_Prod [Tm_Elem "0"; Tm_Elem "2"; Tm_Elem "VAL"]); Tm_Var "myvar"].
Compute (eval_prog [] example_bad_prog3).
Compute (infer_type_prog [] example_bad_prog3).

(* Ещё пример плохой программы - прямое использование Ty_ReadyVar *)
Example example_bad_prog4 : prog := [Tm_Subst Ty_ReadyVar].
Compute (eval_prog [] example_bad_prog4).
Compute (infer_type_prog [] example_bad_prog4).

