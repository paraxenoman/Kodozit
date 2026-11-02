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
  | Ty_Cmd : type
  | Ty_Elem : elem -> type
  | Ty_Prim : prim -> type
  | Ty_Sing : term -> type
  | Ty_Subst : type -> type
  | Ty_Prod : list type -> type
with term : Type :=
(* Синтаксис термов  *)
  | Tm_Var : VarName -> term
  | Tm_DeclVar : VarName -> term -> term
  | Tm_DeclType : TypeName -> type -> term
  | Tm_Cmd : term
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
  | (BindTypeName Y T) :: rest => 
      if eqb X Y then 
        sometype T Γ 
      else 
        type_name_lookup rest X
  | _ :: rest => type_name_lookup rest X
  end.

(* Функция поиска типа переменной в контексте *)
Fixpoint var_type_lookup (Γ : type_context) (x : VarName) : InferTypeResult :=
  match Γ with
  | [] => FailType
  | (BindVarType y T) :: rest => 
      if eqb x y then
        sometype T Γ 
      else 
        var_type_lookup rest x
  | _ :: rest => var_type_lookup rest x
  end.

(* Функция нормализации для типов *)
Fixpoint norm_type (Γ : type_context) (T : type) {struct T} : InferTypeResult :=
    match T with
    | Ty_Var tn => type_name_lookup Γ tn
    | Ty_Sing tm =>
      match infer_type_term Γ tm with
      | FailType => notype
      | TypeCtx tytm _ => sometype (Ty_Sing tm) Γ
      end
    | Ty_Subst ty => norm_type Γ ty
    | Ty_Prod [x] => norm_type Γ x
    | Ty_Prod (p1 :: ps) =>
       let fix norm_list (ts : list type) : option (list type) :=
          match ts with
          | [] => Some []
          | t :: rest =>
            match norm_type Γ t with
            | TypeCtx nrmpt _ =>
                match nrmpt with
                | Ty_Cmd => None
                | _ => 
                    match norm_list rest with
                    | Some nrmpts => Some (nrmpt :: nrmpts)
                    | None => None
                    end
                end
            | FailType => None
            end
          end
        in
          match norm_list (p1 :: ps) with 
          | Some P => sometype (Ty_Prod P) Γ 
          | None => FailType 
          end
    | _ => sometype T Γ
    end
(* Функция вывода и проверки типов *)
with infer_type_term (Γ : type_context) (tm : term)  : InferTypeResult :=
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
              | Ty_Cmd => notype
              | _ => sometype Ty_Cmd (BindVarType x T :: Γ2)
              end
          end
      end
  | Tm_DeclType x T =>
      match type_name_lookup Γ x with
      | TypeCtx _ _ => notype
      | FailType => 
        match norm_type Γ T with
        | TypeCtx TN _ => sometype Ty_Cmd (BindTypeName x TN :: Γ)
        | FailType => notype
        end
      end
  | Tm_Cmd => sometype Ty_Cmd Γ
  | Tm_Elem u => sometype (Ty_Elem u) Γ
  | Tm_Prim p => sometype (Ty_Prim p) Γ
  | Tm_Sing s =>
    match s with
    | Tm_Var _ => notype
    | _ =>
      match infer_type_term Γ s with
      | TypeCtx T _ => 
          match T with
          | Ty_Cmd => notype
          | _ => sometype (Ty_Sing s) Γ
          end
      | FailType => notype
      end
    end
  | Tm_Subst T => 
      match T with
      | Ty_Cmd => notype
      | _ => 
        match norm_type Γ T with 
        | TypeCtx NT _ => sometype (Ty_Subst NT) Γ
        | FailType => notype
        end
      end
  | Tm_Prod [] => sometype Ty_Unit Γ
  | Tm_Prod [x] => 
      match infer_type_term Γ x with
      | TypeCtx T _ => 
          match T with
          | Ty_Cmd => notype
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
                | Ty_Cmd => None
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
      match infer_list (p1 :: ps) with
      | Some P => sometype (Ty_Prod P) Γ 
      | None => FailType 
      end
  end.

Inductive VarValueBinding : Type :=
  | BindVarValue : VarName -> term -> VarValueBinding.

(* Контекст вычислений *)
Definition eval_context := list VarValueBinding.

(* Функция поиска значения переменной в контексте вычислений *)
Fixpoint var_value_lookup (Sigma : eval_context) (x : VarName) : option term :=
  match Sigma with
  | [] => None
  | (BindVarValue y v1) :: rest => 
      if eqb x y then
        Some v1 
      else 
        var_value_lookup rest x
  end.

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
          | ValCtx Tm_Cmd _ => novalue
          | ValCtx v1 Sigma1 => somevalue Tm_Cmd (BindVarValue x v1 :: Sigma1)
          | FailValue => novalue
          end
      end
  | Tm_DeclType _ _ => somevalue Tm_Cmd Sigma
  | Tm_Cmd => somevalue Tm_Cmd Sigma 
  | Tm_Elem e => somevalue (Tm_Elem e) Sigma
  | Tm_Prim p => somevalue (Tm_Prim p) Sigma
  | Tm_Sing s =>
    match s with
    | Tm_Var _ => novalue
    | _ =>
      match eval_term Sigma s with
      | ValCtx Tm_Cmd _ => novalue
      | ValCtx v _ => somevalue (Tm_Sing v) Sigma
      | FailValue => novalue
      end
    end
  | Tm_Subst Ty_Cmd => novalue
  | Tm_Subst T => somevalue (Tm_Subst T) Sigma
  | Tm_Prod p =>
      match p with
      | [] => somevalue Tm_Unit Sigma
      | [x] => 
          match eval_term Sigma x with
          | ValCtx Tm_Cmd _ => novalue
          | v => v
          end
      | _ =>
          let fix eval_list (ts : list term) : option (list term) :=
            match ts with
            | [] => Some []
            | t :: rest =>
                match eval_term Sigma t with
                | ValCtx Tm_Cmd _ => None
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
Example example_good_prog := [
  Tm_DeclVar "sing" (Tm_Sing (Tm_Prod [Tm_Elem "bla"])); 
  Tm_DeclVar "myvar" (Tm_Prod [Tm_Elem "0"; Tm_Var "sing"; Tm_Elem "2"; Tm_Elem "VAL"]);
  Tm_Var "myvar"].
Compute (eval_prog [] example_good_prog).
Compute (infer_type_prog [] example_good_prog).

(* Плохая программа - undefined variable bad *)
Example example_bad_prog := (Tm_DeclVar "bed" (Tm_Elem "()") :: Tm_Var "bad" :: []).
Compute (eval_prog [] example_bad_prog).
Compute (infer_type_prog [] example_bad_prog).

(* Плохая программа - объявление переменных не на топлевеле *)
Example example_bad_prog2 := [Tm_Prod [Tm_Elem ""; Tm_DeclVar "bed" (Tm_Elem "()")]].
Compute (eval_prog [] example_bad_prog2).
Compute (infer_type_prog [] example_bad_prog2).

(* Плохая программа - затенение переменных *)
Example example_bad_prog3 := [Tm_DeclVar "input" (Tm_Elem "bla");
  Tm_DeclVar "input" (Tm_Prod [Tm_Elem "0"; Tm_Elem "2"; Tm_Elem "VAL"]);
  Tm_Var "myvar"].
Compute (eval_prog [] example_bad_prog3).
Compute (infer_type_prog [] example_bad_prog3).

(* Плохая программа - прямое использование Ty_Cmd *)
Example example_bad_prog4 : prog := [Tm_Subst Ty_Cmd].
Compute (eval_prog [] example_bad_prog4).
Compute (infer_type_prog [] example_bad_prog4).

(* Плохая программа - использование переменной в Tm_Sing *)
Example example_bad_prog5 := [
  Tm_DeclVar "input" (Tm_Elem "bla"); 
  Tm_DeclVar "myvar" (Tm_Prod [Tm_Elem "0"; Tm_Sing (Tm_Var "input"); Tm_Elem "2"; Tm_Elem "VAL"]);
  Tm_Var "myvar"].
Compute (eval_prog [] example_bad_prog5).
Compute (infer_type_prog [] example_bad_prog5).