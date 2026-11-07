(* Kodozit.Seos Formal Theory @ Paraxenoman *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Definition TypeName : Type := string.
Definition VarName : Type := string.
Definition elem : Type := string.

Inductive prim : Type :=
  | Prm_Left : prim
  | Prm_Right : prim.

(* Синтаксис типов  *)
Inductive type : Type :=
  | Ty_Error : type
  | Ty_Abbr : TypeName -> type
  | Ty_Cmd : type
  | Ty_Elem : elem -> type
  | Ty_Prim : prim -> type
  | Ty_Sing : term -> type
  | Ty_Subst : type -> type
  | Ty_Prod : list type -> type
with term : Type :=
(* Синтаксис термов  *)
  | Tm_Error : term
  | Tm_Var : VarName -> term
  | Tm_DeclVar : VarName -> term -> term
  | Tm_NewTypeAbbr : TypeName -> type -> term
  | Tm_Cmd : term
  | Tm_Elem : elem -> term
  | Tm_Prim : prim -> term
  | Tm_Sing : term -> term
  | Tm_Subst : type -> term
  | Tm_Prod : list term -> term.

Notation Tm_Unit := (Tm_Prod []).
Notation Ty_Unit := (Ty_Prod []).

Inductive TypeBinding : Type :=
  | BindTypeAbbr : TypeName -> type -> TypeBinding
  | BindVarType : VarName -> type -> TypeBinding
  | BindCombType : list type -> type -> TypeBinding.

(* Контекст типизации *)
Definition type_context := list TypeBinding.

Inductive InferTypeResult : Type :=
  | TypeCtx : type -> type_context -> InferTypeResult
  | FailType : InferTypeResult.

Definition sometype t Γ := TypeCtx t Γ.
Definition notype := FailType.

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
  | Tm_NewTypeAbbr _ _ => somevalue Tm_Cmd Sigma
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
  | Tm_Error => novalue
  end.

(* Функция равенства двух списков *)
Fixpoint list_eqb {A} (feq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 =>
      feq x1 x2 && list_eqb feq t1 t2
  | _, _ => false
  end.

(* Функция равенства примов *)
Definition prim_beq (p1 p2 : prim) : bool :=
  match p1, p2 with
  | Prm_Left, Prm_Left => true
  | Prm_Right, Prm_Right => true
  | _, _ => false
  end.

(* Функция нормализации для типов *)
Fixpoint norm_type (Γ : type_context) (T : type) {struct T} : option type :=
    match T with
    | Ty_Error => None
    | Ty_Abbr tn => type_abbr_lookup Γ tn
    | Ty_Sing tm =>
      match infer_type_term Γ tm with
      | FailType => None
      | TypeCtx tytm _ => Some (Ty_Sing tm)
      end
    | Ty_Subst ty => 
        match norm_type Γ ty with
        | None => None
        | Some nrmty => Some (Ty_Subst nrmty)
        end
        
    | Ty_Prod [x] => norm_type Γ x
    | Ty_Prod (p1 :: ps) =>
       let fix norm_list (ts : list type) : option (list type) :=
          match ts with
          | [] => Some []
          | t :: rest =>
            match norm_type Γ t with
            | Some nrmpt =>
                match nrmpt with
                | Ty_Cmd => None
                | _ => 
                    match norm_list rest with
                    | Some nrmpts => Some (nrmpt :: nrmpts)
                    | None => None
                    end
                end
            | None => None
            end
          end
        in
          match norm_list (p1 :: ps) with 
          | Some P => Some (Ty_Prod P) 
          | None => None
          end
    | _ => Some T
    end
(* Функция вывода и проверки типов *)
with infer_type_term (Γ : type_context) (tm : term) : InferTypeResult :=
  match tm with
  | Tm_Error => FailType
  | Tm_Var x => 
      match var_type_lookup Γ x with
      | Some T => sometype T Γ
      | None => notype
      end
  | Tm_DeclVar x tm =>
      match var_type_lookup Γ x with
      | Some _ => notype
      | None =>
          match infer_type_term Γ tm with
          | FailType => notype
          | TypeCtx T Γ2 => 
              match T with
              | Ty_Cmd => notype
              | _ => sometype Ty_Cmd (BindVarType x T :: Γ2)
              end
          end
      end
  | Tm_NewTypeAbbr x T =>
      match type_abbr_lookup Γ x with
      | Some _ => notype
      | None => 
        match norm_type Γ T with
        | Some TN => sometype Ty_Cmd (BindTypeAbbr x TN :: Γ)
        | None => notype
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
        | Some NT => sometype (Ty_Subst NT) Γ
        | None => notype
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

(* Функция булевого равенства для термов без приведения в номальную форму *)
Fixpoint term_beq (it1 it2 : term) : bool :=
      match it1, it2 with
      | Tm_Var vn1, Tm_Var vn2 => eqb vn1 vn2
      | Tm_Elem e1, Tm_Elem e2 => eqb e1 e2
      | Tm_Prim p1, Tm_Prim p2 => prim_beq p1 p2
      | Tm_Sing tm1, Tm_Sing tm2 => term_beq tm1 tm2
      | Tm_Subst tp1, Tm_Subst tp2 => type_beq tp1 tp2
      | Tm_Prod l1, Tm_Prod l2 => list_eqb term_beq l1 l2
      | _, _ => false
      end
(* Функция булевого равенства для типов без нормализации *)
with type_beq (it1 it2 : type) : bool := 
      match it1, it2 with
      | Ty_Abbr vn1, Ty_Abbr vn2 => eqb vn1 vn2
      | Ty_Elem e1, Ty_Elem e2 => eqb e1 e2
      | Ty_Prim p1, Ty_Prim p2 => prim_beq p1 p2
      | Ty_Sing tm1, Ty_Sing tm2 => term_beq tm1 tm2
      | Ty_Subst tp1, Ty_Subst tp2 => type_beq tp1 tp2
      | Ty_Prod l1, Ty_Prod l2 => list_eqb type_beq l1 l2
      | _, _ => false
      end.

(* Функция булевого равенства для нормальных форм термов *)
Definition norm_term_beq (ctx : eval_context) (it1 it2 : term) : bool :=
  let mnt1 := eval_term ctx it1 
    in let mnt2 := eval_term ctx it2
      in
        match mnt1, mnt2 with
        | ValCtx nt1 _, ValCtx nt2 _ => term_beq nt1 nt2
        | _, _ => false
        end.

(* Функция булевого равенства для нормализованых типов *)
Definition norm_type_beq (ctx : type_context) (it1 it2 : type) : bool :=
  let mnt1 := norm_type ctx it1 
    in let mnt2 := norm_type ctx it2
      in
        match mnt1, mnt2 with
        | Some nt1, Some nt2 => type_beq nt1 nt2
        | _, _ => false
        end.

Definition prog : Type := list term.

(*
  Окружение уже раскрытых определений типов.
  В отличие от type_context, здесь хранятся именно определения имён типов.
*)
Definition type_def_context : Type :=
  list (TypeName * type).

(*
  Окружение уже раскрытых определений термов.
*)
Definition term_def_context : Type :=
  list (VarName * term).


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


Fixpoint lookup_term_def
    (Sigma : term_def_context)
    (x : VarName)
  : option term :=
  match Sigma with
  | [] => None
  | (y, tm) :: rest =>
      if eqb x y
      then Some tm
      else lookup_term_def rest x
  end.

Fixpoint unfold_type
    (Sigma : term_def_context)
    (Delta : type_def_context)
    (T : type) {struct T}
  : type :=
  match T with
  | Ty_Error => Ty_Error
  | Ty_Abbr X =>
      match lookup_type_def Delta X with
      | Some T' => T'
      | None => Ty_Abbr X
      end

  | Ty_Cmd => Ty_Cmd
  | Ty_Elem e => Ty_Elem e
  | Ty_Prim p => Ty_Prim p

  | Ty_Sing tm =>
      Ty_Sing (unfold_term Sigma Delta tm)

  | Ty_Subst T1 =>
      match norm_type [] (Ty_Subst (unfold_type Sigma Delta T1)) with
      | Some ntp => ntp
      | _ => Ty_Error
      end

  | Ty_Prod Ts =>
      let fix go (xs : list type) : list type :=
          match xs with
          | [] => []
          | x :: rest =>
              unfold_type Sigma Delta x :: go rest
          end
      in Ty_Prod (go Ts)
  end

with unfold_term
    (Sigma : term_def_context)
    (Delta : type_def_context)
    (tm : term) {struct tm}
  : term :=
  match tm with
  | Tm_Error => Tm_Error
  | Tm_Var x =>
      match lookup_term_def Sigma x with
      | Some tm' => tm'
      | None => Tm_Var x
      end

  | Tm_DeclVar x rhs =>
      Tm_DeclVar x (unfold_term Sigma Delta rhs)

  | Tm_NewTypeAbbr X T =>
      Tm_NewTypeAbbr X (unfold_type Sigma Delta T)

  | Tm_Cmd => Tm_Cmd
  | Tm_Elem e => Tm_Elem e
  | Tm_Prim p => Tm_Prim p

  | Tm_Sing s =>
      match eval_term [] (Tm_Sing (unfold_term Sigma Delta s)) with
      | ValCtx ntm _ => ntm
      | _ => Tm_Error
      end

  | Tm_Subst T =>
      match norm_type [] (unfold_type Sigma Delta T) with
      | Some ntp => Tm_Subst ntp
      | _ => Tm_Error
      end

  | Tm_Prod ts =>
      let fix go (xs : list term) : list term :=
          match xs with
          | [] => []
          | x :: rest =>
              unfold_term Sigma Delta x :: go rest
          end
      in Tm_Prod (go ts)
  end.


Fixpoint unfold_prog_aux
    (Sigma : term_def_context)
    (Delta : type_def_context)
    (prg : prog) {struct prg}
  : prog :=
  match prg with
  | [] =>
      []

  | Tm_DeclVar x rhs :: rest =>
      let rhs' := unfold_term Sigma Delta rhs in
      Tm_DeclVar x rhs'
        :: unfold_prog_aux
             ((x, rhs') :: Sigma)
             Delta
             rest

  | Tm_NewTypeAbbr X T :: rest =>
      let T' := unfold_type Sigma Delta T in
      Tm_NewTypeAbbr X T'
        :: unfold_prog_aux
             Sigma
             ((X, T') :: Delta)
             rest

  | tm :: rest =>
      unfold_term Sigma Delta tm
        :: unfold_prog_aux Sigma Delta rest
  end.


Definition unfold_prog (prg : prog) : prog :=
  unfold_prog_aux [] [] prg.

(* Вспомогательная функция проверки типа программы *)
Fixpoint infer_type_prog_aux (Γ : type_context) (prg : prog) : option type :=
  let fix f g p {struct p} := match p with
  | [] => TypeCtx Ty_Unit g
  | [t] => infer_type_term g t
  | t :: rest =>
      match infer_type_term g t with
      | TypeCtx _ Γ2 =>
           match infer_type_prog_aux Γ2 rest with
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

(* Вспомогательная функция вычисления программы *)
Fixpoint eval_prog_aux (Sigma : eval_context) (prg : prog) : option term :=
  let fix f s p {struct p} := match p with
  | [] => ValCtx Tm_Unit s
  | [t] => eval_term s t
  | t :: rest =>
      match eval_term s t with
      | ValCtx _ s1 => 
          match eval_prog_aux s1 rest with
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

(* Основная функция проверки типа программы *)
Definition infer_type_prog (Γ : type_context) (prg : prog) : option type :=
  infer_type_prog_aux Γ (unfold_prog prg).

(* Основная функция вычисления программы *)
Definition eval_prog (Sigma : eval_context) (prg : prog) : option term :=
  eval_prog_aux Sigma (unfold_prog prg).

(* Тривиальный пример хорошей программы *)
Example example_good_prog := [
  Tm_DeclVar "sing" (Tm_Sing (Tm_Prod [Tm_Elem "bla"])); 
  Tm_DeclVar "myvar" (Tm_Prod [Tm_Subst (Ty_Prod [Ty_Elem "one"]); Tm_Elem "0"; Tm_Var "sing"; Tm_Elem "2"; Tm_Elem "VAL"]);
  Tm_Var "myvar"].
Compute (infer_type_prog [] example_good_prog).
Compute (eval_prog [] example_good_prog).

(* Хорошая программа - использование переменной в Tm_Sing *)
Example example_good_prog2 := [
  Tm_DeclVar "input" (Tm_Elem "bla"); 
  Tm_DeclVar "myvar" (Tm_Prod [Tm_Elem "0"; Tm_Sing (Tm_Var "input"); Tm_Elem "2"; Tm_Elem "VAL"]);
  Tm_Var "myvar"].
Compute (infer_type_prog [] example_good_prog2).
Compute (eval_prog [] example_good_prog2).

(* Плохая программа - undefined variable bad *)
Example example_bad_prog := (Tm_DeclVar "bed" (Tm_Elem "()") :: Tm_Var "bad" :: []).
Compute (infer_type_prog [] example_bad_prog).
Compute (eval_prog [] example_bad_prog).

(* Плохая программа - объявление переменных не на топлевеле *)
Example example_bad_prog2 := [Tm_Prod [Tm_Elem ""; Tm_DeclVar "bed" (Tm_Elem "()")]].
Compute (infer_type_prog [] example_bad_prog2).
Compute (eval_prog [] example_bad_prog2).

(* Плохая программа - затенение переменных *)
Example example_bad_prog3 := [Tm_DeclVar "input" (Tm_Elem "bla");
  Tm_DeclVar "input" (Tm_Prod [Tm_Elem "0"; Tm_Elem "2"; Tm_Elem "VAL"]);
  Tm_Var "myvar"].
Compute (infer_type_prog [] example_bad_prog3).
Compute (eval_prog [] example_bad_prog3).

(* Плохая программа - прямое использование Ty_Cmd *)
Example example_bad_prog4 : prog := [Tm_Subst Ty_Cmd].
Compute (infer_type_prog [] example_bad_prog4).
Compute (eval_prog [] example_bad_prog4).




