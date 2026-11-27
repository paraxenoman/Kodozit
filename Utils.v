Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope list_scope.

Fixpoint list_eqb {A : Type} (feq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => feq x1 x2 && list_eqb feq t1 t2
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