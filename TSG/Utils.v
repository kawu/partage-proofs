(* From Coq Require Import Arith.Arith. *)
From Coq Require Import Reals.Reals.
From Coq Require Import Lists.List.
Import ListNotations.


(**
  Definitions
**)


Fixpoint cat_maybes {A : Type} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some h :: t => h :: cat_maybes t
  | None :: t => cat_maybes t
  end.


Definition map_maybe {A B : Type} (f : A -> option B) (l : list A) : list B :=
  cat_maybes (map f l).


Fixpoint drop {A : Type} (k : nat) (l : list A) : list A :=
  match k, l with
  | 0, _ => l
  | _, _ :: t => drop (k-1) t
  | _, [] => []
  end.

(* Open Scope R_scope. *)

(** Minimum nat *)
Fixpoint minimum (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | x :: t =>
    match minimum t with
    | None => Some x
    | Some y => Some (min x y) (* Rmin for Reals *)
    end
  end.


(** Maximum nat *)
Fixpoint maximum (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | x :: t =>
    match maximum t with
    | None => Some x
    | Some y => Some (max x y)
    end
  end.

(* Close Scope R_scope. *)


(* fmap for an option *)
Definition fmap
  {A B : Type} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some v => Some (f v)
  end.


(**
  Lemmas
**)


Open Scope R_scope.


Lemma minus_le_plus : forall x y z,
  y <= x ->
    (x - y) + z = (x + z) - y.
Proof. Admitted.
(*
  intros x y z. intros H.
  induction z as [|z' IH].
  - rewrite plus_0_r. rewrite plus_0_r. reflexivity.
  - rewrite Nat.add_succ_r.
    rewrite Nat.add_succ_r.
    rewrite IH.
    rewrite minus_Sn_m.
    + reflexivity.
    + transitivity x.
      * apply H.
      * apply le_plus_l.
Qed. *)


Lemma plus_minus : forall x y z,
  (x + y) - (y + z) = x - z.
Proof. Admitted.
(*
  intros x y z.
  induction y as [|y' IH].
  - simpl. rewrite plus_0_r. reflexivity.
  - simpl. rewrite <- plus_Snm_nSm. simpl. apply IH.
Qed. *)


About Rplus_comm.


Lemma fold_left_plus : forall (x : R) (l : list R),
  fold_left Rplus l x = fold_left Rplus l 0 + x.
Proof.
  intros x l.
  generalize dependent x.
  induction l as [|h t IH].
  - intros x. simpl. rewrite Rplus_0_l. reflexivity.
  - intros x. simpl. rewrite IH. rewrite Rplus_0_l.
    rewrite (IH h). rewrite -> Rplus_assoc.
    rewrite (Rplus_comm x h). reflexivity.
Qed.


Close Scope R_scope.