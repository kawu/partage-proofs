From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

From LF Require Import Utils.
From LF Require Import LE.
From LF Require Import App.
From LF Require Import Grammar.
From LF Require Import Span.
From LF Require Import Cost.

(** Amortized weight of the given passive parsing configuration *)
Definition amort_weight {vt nt} (g : @Grammar vt nt) (n : vt) : weight :=
  tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup g n).


(** Amortized weight of the given active parsing configuration *)
Definition amort_weight' {vt nt} (g : @Grammar vt nt) (r : vt*nat) : weight :=
  let n := fst r
  in tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup' g r).


Lemma shift_amort_weight : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r' = Some (v, r) ->
    amort_weight' g r = amort_weight' g r' + costs g (inf g v).
Proof.
  intros vt nt g r r' v H.
  unfold amort_weight'.
  apply shift_preserves_head in H as H'.
  rewrite H'.
  apply shift_cost_sup in H as H''.
  rewrite (minus_le_plus
          (tree_weight g (fst r) + min_arc_weight g (anchor g (fst r)))
          (costs g (sup' g r'))).
  - rewrite H''. rewrite plus_minus. reflexivity.
  - destruct (sup' g r') eqn:E.
    + unfold costs. simpl. apply Peano.le_0_n.
    + apply sup'_destr in E as [E1 E2].
      rewrite E2. unfold costs.
      simpl. unfold cost. rewrite plus_comm.
      apply (combine_leb).
        * apply min_tree_weight_leb.
          rewrite E1. rewrite H'. reflexivity.
        * rewrite E1. rewrite H'. reflexivity.
Qed.


Lemma shift_amort_weight' : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r = Some (v, r') ->
    amort_weight g v + costs g (inf' g r) = amort_weight' g r'.
Proof.
  intros vt nt g r r' v H.
  unfold amort_weight. unfold amort_weight'.
  apply shift_preserves_tree_weight in H as H1.
  rewrite <- H1.
  apply shift_preserves_anchor in H as H2.
  rewrite <- H2.
  apply shift_cost_sup' in H as H3.
  rewrite (minus_le_plus _ (costs g (sup g v))).
  - rewrite H3. rewrite plus_minus. reflexivity.
  - destruct (sup g v) eqn:E.
    + unfold costs. simpl. apply le_0_n.
    + apply sup_destr in E as [E1 E2].
      rewrite E2. unfold costs.
      simpl. unfold cost. rewrite plus_comm.
      apply (combine_leb).
        * apply min_tree_weight_leb.
          rewrite E1. reflexivity.
        * rewrite E1. reflexivity.
Qed.


Lemma amort_weight_complete : forall {vt nt}
  (g : @Grammar vt nt) (r : vt*nat),
    shift g r = None ->
      amort_weight g (fst r) = amort_weight' g r.
Proof.
  intros vt nt g r.
  intros H.
  unfold amort_weight.
  unfold amort_weight'.
  apply shift_sup_passive in H.
  rewrite H. reflexivity.
Qed.
