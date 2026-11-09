(* Kodozit.Seos Formal Theory @ Paraxenoman *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
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
  | T_Abbr : TypeName -> type
  | T_Elem : elem -> type
  | T_Prim : prim -> type
  | T_Sing : value -> type
  | T_TRep : type -> type
  | T_Prod : list type -> type
  | T_Comb : TypeName -> type
with expr : Type :=
(* Синтаксис выражений  *)
  | E_Var : VarName -> expr
  | E_Elem : elem -> expr
  | E_Prim : prim -> expr
  | E_Sing : expr -> expr
  | E_TRep : type -> expr
  | E_Prod : list expr -> expr
  | E_Comb : list expr -> expr
(* Синтаксис значений *)
with value : Type :=
  | V_Elem : elem -> value
  | V_Prim : prim -> value
  | V_Sing : value -> value
  | V_TRep : type -> value
  | V_Prod : list value -> value
  | V_Comb : list value -> value.

(* Синтаксис комманд *)
Inductive command : Type :=
  | C_DeclVar : VarName -> expr -> command
  | C_NewTypeAbbr : TypeName -> type -> command
  | C_DeclCombType : TypeName -> list type -> command
  | C_Eval : expr -> command.

Inductive error : Type :=
  | Err_UnboundVar : VarName -> error
  | Err_UnboundType : TypeName -> error
  | Err_DuplicateVar : VarName -> error
  | Err_DuplicateType : TypeName -> error
  | Err_DuplicateCombSignature : TypeName -> list type -> error
  | Err_UnknownCombSignature : error
  | Err_InvalidType : error
  | Err_TypeMismatch : error
  | Err_UnexpectedVar : VarName -> error.

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
  | BindCombType : TypeName -> list type -> TypeBinding.

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
  | T_Sing tm1, T_Sing tm2 => value_beq tm1 tm2
  | T_TRep tp1, T_TRep tp2 => type_beq tp1 tp2
  | T_Prod l1, T_Prod l2 => list_eqb type_beq l1 l2
  | T_Comb vn1, T_Comb vn2 => eqb vn1 vn2
  | _, _ => false
  end
(* Функция булевого равенства для значений *)
with value_beq (it1 it2 : value) : bool :=
  match it1, it2 with
  | V_Elem e1, V_Elem e2 => eqb e1 e2
  | V_Prim p1, V_Prim p2 => prim_beq p1 p2
  | V_Sing tm1, V_Sing tm2 => value_beq tm1 tm2
  | V_TRep tp1, V_TRep tp2 => type_beq tp1 tp2
  | V_Prod l1, V_Prod l2 => list_eqb value_beq l1 l2
  | V_Comb l1, V_Comb l2 => list_eqb value_beq l1 l2
  | _, _ => false
  end.

(* Функция поиска типа комбинации *)
Fixpoint type_comb_lookup 
      (Γ : type_context) 
      (lst : list type) 
      {struct Γ} : option TypeName :=
  match Γ with
  | [] => None
  | (BindCombType TN LST) :: rest => 
      if list_eqb type_beq lst LST then 
        Some TN
      else 
        type_comb_lookup rest lst
  | _ :: rest => type_comb_lookup rest lst
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
  | (BindCombType tn _) :: rest => 
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

Definition type_declared (ctx : type_context) (intn : TypeName) : bool :=
  comb_type_declared ctx intn || type_abbr_declared ctx intn.

(* Функция нормализации для типов *)
Fixpoint norm_type (Γ : type_context) (T : type) {struct T} : result type :=
    match T with
    | T_Abbr tn => 
        if type_abbr_lookup Γ tn then 
          Ok (T_Abbr tn) 
        else 
          Err (Err_UnboundType tn)
    | T_Sing tm =>
      match infer_type_value Γ tm with
      | Err e => Err e
      | Ok _ => Ok (T_Sing tm)
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
    | _ => Ok T
    end
(* Функция вывода и проверки типов *)
with infer_type_value (Γ : type_context) (tm : value) : result type :=
  match tm with
  | V_Elem u => Ok (T_Elem u)
  | V_Prim p => Ok (T_Prim p)
  | V_Sing s =>
      match infer_type_value Γ s with
      | Ok T => Ok (T_Sing s)
      | Err e => Err e
      end
  | V_TRep T => 
      match norm_type Γ T with 
      | Ok NT => Ok (T_TRep NT)
      | Err e => Err e
      end
  | V_Prod [] => Ok T_Unit
  | V_Prod [x] => 
      match infer_type_value Γ x with
      | Ok T => Ok T
      | Err e => Err e
      end
  | V_Prod (p1 :: ps) =>
      match infer_list infer_type_value Γ (p1 :: ps) with
      | Ok P => Ok (T_Prod P) 
      | Err e => Err e
      end
  | V_Comb lst =>
      match infer_list infer_type_value Γ lst with
      | Ok wtlst => 
          match type_comb_lookup Γ wtlst with
          | Some TN => Ok (T_Comb TN)
          | None => Err (Err_UnknownCombSignature)
          end
      | Err e => Err e
      end 
  end.

Fixpoint infer_type_expr (Γ : type_context) (tm : expr) : result type :=
  match tm with
  | E_Var x => 
      match var_type_lookup Γ x with
      | Some T => Ok T
      | None => Err (Err_UnboundVar x)
      end 
  | E_Elem u => Ok (T_Elem u)
  | E_Prim p => Ok (T_Prim p)
  | E_Sing s =>
      match s with
      | E_Var x => Err (Err_UnexpectedVar x)
      | e => infer_type_expr Γ e
      end
  | E_TRep T => 
      match norm_type Γ T with 
      | Ok NT => Ok (T_TRep NT)
      | Err e => Err e
      end
  | E_Prod [] => Ok T_Unit
  | E_Prod [x] => 
      match infer_type_expr Γ x with
      | Ok T => Ok T
      | Err e => Err e
      end
  | E_Prod (p1 :: ps) =>
      match infer_list infer_type_expr Γ (p1 :: ps) with
      | Ok P => Ok (T_Prod P) 
      | Err e => Err e
      end
  | E_Comb lst =>
      match infer_list infer_type_expr Γ lst with
      | Ok wtlst => 
          match type_comb_lookup Γ wtlst with
          | Some TN => Ok (T_Comb TN)
          | None => Err (Err_UnknownCombSignature)
          end
      | Err e => Err e
      end 
  end.

(* Функция вычисления для выражений *) 
Fixpoint eval_expr (Sigma : eval_context) (tm : expr) : result value :=
  match tm with
  | E_Var x =>
      match var_value_lookup Sigma x with
      | Some v => Ok v
      | None => Err (Err_UnboundVar x)
      end
  | E_Elem e => Ok (V_Elem e)
  | E_Prim p => Ok (V_Prim p)
  | E_Sing s =>
      match eval_expr Sigma s with
      | Ok v => Ok (V_Sing v)
      | Err e => Err e
      end
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
  | E_Comb lst =>
      match (eval_expr_list eval_expr Sigma lst) with
      | Ok l => Ok (V_Comb l)
      | Err e => Err e
      end
  end.

Definition exec_command (st : machine_state) (cmd : command) : result machine_state :=
  let Γ := st.(ms_type_ctx) in
  let Sigma := st.(ms_eval_ctx) in
  match cmd with
  | C_DeclVar x inex =>
      match var_value_lookup Sigma x, var_type_lookup Γ x with
      | None, None =>
          match eval_expr Sigma inex with
          | Ok ex => 
              match infer_type_value Γ ex, (Ok ex) with
              | Ok t, Ok v => Ok {| 
                  ms_type_ctx := (BindVarType x t :: Γ);
                  ms_eval_ctx := (BindVarValue x v :: Sigma);
                  ms_last_type := st.(ms_last_type);
                  ms_last_value := st.(ms_last_value) |}
              | Err er, _ => Err er
              | _, Err er => Err er
              end
          | Err e => Err e
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
              ms_last_type := st.(ms_last_type);
              ms_last_value := st.(ms_last_value) |}
        | Err e => Err e
        end
      end
  | C_DeclCombType tn lst => 
      if type_declared Γ tn then
        Err (Err_DuplicateType tn)
      else
      match norm_list norm_type Γ lst with
      | Ok nrmlst =>
        match type_comb_lookup Γ nrmlst with
        | Some _ => Err (Err_DuplicateCombSignature tn lst)
        | None => 
             Ok {| 
              ms_type_ctx := (BindCombType tn nrmlst :: Γ);
              ms_eval_ctx := Sigma;
              ms_last_type := st.(ms_last_type);
              ms_last_value := st.(ms_last_value) |}
        end
      | Err e => Err e
      end
  | C_Eval e =>
      match infer_type_expr Γ e, eval_expr Sigma e with
      | Ok T, Ok v => Ok {| 
          ms_type_ctx := Γ;
          ms_eval_ctx := Sigma;
          ms_last_type := T;
          ms_last_value := v |}
      | Err er, _ => Err er
      | _, Err er => Err er
      end
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
      | None => Err (Err_UnboundType X)
      end

  | T_Elem e => Ok (T_Elem e)
  | T_Prim p => Ok (T_Prim p)

  | T_Sing tm => Ok (T_Sing tm)

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
  | T_Comb tn => Ok (T_Comb tn)
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

  | E_Sing s =>
      match unfold_expr Sigma Delta s with
      | Ok ns => Ok (E_Sing ns)
      | Err e => Err e
      end

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
  
  | E_Comb lst => 
      match unfold_list unfold_expr Sigma Delta lst with
      | Ok newlst => Ok (E_Comb newlst)
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
          unfold_prog_aux
             ((x, rhs') :: Sigma)
             Delta
             rest
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

  | C_DeclCombType tn lst :: rest =>
      match unfold_type Sigma Delta (T_Prod lst) with
      | Ok (T_Prod newlst) => 
          match unfold_prog_aux Sigma Delta rest with
          | Ok restprg => Ok (C_DeclCombType tn newlst :: restprg)
          | Err e => Err e
          end
      | Ok _ => Err (Err_TypeMismatch)
      | Err e => Err e
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
  end.

Definition unfold_prog (prg : prog) : result prog :=
  unfold_prog_aux [] [] prg.

Record Prg_Result := {prog_type : type; prog_val : value}.

Fixpoint compile_prog_aux (st : machine_state) (inprg : prog) {struct inprg} : result machine_state :=
  match inprg with
  | [] => Ok {| 
          ms_type_ctx := st.(ms_type_ctx);
          ms_eval_ctx := st.(ms_eval_ctx);
          ms_last_type := st.(ms_last_type);
          ms_last_value := st.(ms_last_value) |}
  | [c] => exec_command st c
  | (curcmd :: rest) =>
      match exec_command st curcmd with
      | Ok newst => compile_prog_aux newst rest
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
Example example_good_prog := [
  C_DeclVar "sing" (E_Sing (E_Prod [E_Elem "bla"])); 
  C_DeclVar "myvar" (E_Prod [E_TRep (T_Prod [T_Elem "one"]); E_Elem "0"; E_Var "sing"; E_Elem "2"; E_Elem "VAL"]);
  C_Eval (E_TRep (T_Prod [T_Elem "one"])); C_Eval (E_Var "myvar") ].
Compute (compile_prog example_good_prog).

(* Хорошая программа - использование переменной в E_Sing *)
Example example_good_prog2 := [
  C_DeclVar "input" (E_Elem "bla"); 
  C_DeclVar "myvar"
    (E_Prod [E_Elem "0"; E_Sing (E_Var "input"); E_Elem "2"; E_Elem "VAL"]);
  C_Eval (E_Var "myvar")].
Compute (compile_prog example_good_prog2).

(* Хорошая программа -  объявление типов-комбинаций *)
Example example_good_prog3 := [
  C_DeclVar "p" (E_Prod [E_Elem "Nat"]);
  C_NewTypeAbbr "TP" (T_Prod [T_Elem "Nat"]);
  C_DeclCombType "NatZero" [T_Elem "Zero"; T_Prod [T_Abbr "TP"]];
  C_DeclVar "n" (E_Comb [E_Elem "Zero"; E_Elem "Nat"]);
  C_DeclVar "s" (E_TRep (T_Comb "NatZero"));
  C_Eval (E_Prod [E_Var "n"; E_Var "s"]) 
].
Compute (compile_prog example_good_prog3).

(* Плохая программа - undefined variable bad *)
Example example_bad_prog := [
  C_DeclVar "bed" (E_Elem "()"); C_Eval (E_Var "bad")].
Compute (compile_prog example_bad_prog).

(* Плохая программа - затенение переменных *)
Example example_bad_prog2 := [
  C_DeclVar "input" (E_Elem "bla");
  C_DeclVar "input" (E_Prod [E_Elem "0"; E_Elem "2"; E_Elem "VAL"]);
  C_Eval (E_Var "myvar")
].
Compute (compile_prog example_bad_prog2).

(* Плохая программа - объявление типов и их синонимов с занятыми именами *)
Example example_bad_prog3 : prog := [
  C_NewTypeAbbr "NatZero" (T_Prod [T_Elem "Nat"]);
  C_DeclCombType "NatZero" [T_Elem "Zero"; (T_Prod [T_Elem "Nat"])];
  C_DeclVar "p" (E_Prod [E_Elem "Nat"]);
  C_Eval (E_Var "p")
].
Compute (compile_prog example_bad_prog3).

(* Плохая программа - объявление типов комбинаций с одинаковым набором типов *)
Example example_bad_prog4 : prog := [
  C_NewTypeAbbr "TP" (T_Prod [T_Elem "Nat"]);
  C_DeclCombType "NatZero" [T_Elem "Zero"; T_Elem "Nat"];
  C_DeclCombType "NatZeroCopy" [T_Elem "Zero"; T_Prod [T_Abbr "TP"]]
].
Compute (compile_prog example_bad_prog4).
