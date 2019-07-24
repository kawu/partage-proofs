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
From LF Require Import Amort.


(** Value of the heuristic for the given active item *)
Definition heuristic {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term) : weight :=
    amort_weight' g r + costs g (rest g i j).


(** Item's total weight, i.e., the inside weight + the heuristic estimation *)
Definition total {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term)
  (w : weight) (* inside weight *)
  : weight :=
    w + heuristic g r i j.


(** Inference rules for chart items.

We thread the previous max total weight through the inference rules
in order to be able to easily check the monotonicity of the system.

*)
Inductive item {vt nt}
   : @Grammar vt nt
    (* the underlying grammar *)
  -> vt*nat -> term -> term
    (* rule, starting position, ending position *)
  -> weight
    (* inside weight *)
  -> weight
    (* previous max total weight *)
  -> Prop :=
  | axiom (g : @Grammar vt nt) (r : vt*nat) (i : term)
      (I: In r (rules g))
      (L: i <= term_max g) :
        item g r i i 0 0
  | scan (g : @Grammar vt nt)
      (r r' : vt*nat) (i : term) (j : term) (v : vt) (w _t : weight)
      (P: item g r i j w _t)
      (L: j <= term_max g)
      (E1: shift g r = Some (v, r'))
      (E2: label g v = Terminal j) :
        item g r' i (S j) w
          (total g r i j w)
  | pseudo_subst
      (g : @Grammar vt nt) (l r l' : vt*nat) (i j k : term) (w1 w2 _t1 _t2 : weight)
      (LP: item g l i j w1 _t1)
      (RP: item g r j k w2 _t2)
      (L: shift g r = None)
      (E: shift g l = Some (fst r, l')) :
        item g l' i k (w1 + w2)
          (max (total g l i j w1) (total g r j k w2))
  | subst
      (g : @Grammar vt nt) (l r l' : vt*nat) (i j k : term) (v : vt)
      (w1 w2 _t1 _t2 : weight)
      (LP: item g l i j w1 _t1)
      (RP: item g r j k w2 _t2)
      (L1: shift g r = None)
      (L2: root g (fst r) = true)
      (L3: shift g l = Some (v, l'))
      (L4: leaf g v = true)
      (E: label g v = label g (fst r)) :
        item g l' i k (w1 + w2 + omega g (fst r) (fst l))
          (max (total g l i j w1) (total g r j k w2)).


Theorem item_i_le_j : forall {vt nt} r i j w t (g : @Grammar vt nt)
  (H: @item vt nt g r i j w t),
    i <= j.
Proof.
  intros vt nt r i j w t g.
  intros eta.
  induction eta
    as [ g r' i' I L
       | g r1 r2 i' j' v w' _t' P IHP L E1 E2
       | g l r' l' i' j' k w1 w2 _t1 _t2 LP IHL RP IHP L E
       | g l r l' i j k v w1 w2 _t1 _t2 LP IHL RP IHP L1 L2 L3 L4 E
       ].
  - reflexivity.
  - apply le_S. apply IHP.
  - transitivity j'. { apply IHL. } { apply IHP. }
  - transitivity j. { apply IHL. } { apply IHP. }
Qed.


Theorem item_j_le_term_max : forall {vt nt} r i j w t (g : @Grammar vt nt)
  (H: @item vt nt g r i j w t),
    j <= term_max g + 1.
Proof.
  intros vt nt r i j w t g.
  intros eta.
  induction eta
    as [ g r' i' I L
       | g r1 r2 i' j' v w' _t' P IHP L E1 E2
       | g l r' l' i' j' k w1 w2 _t1 _t2 LP IHL RP IHP L E
       | g l r l' i j k v w1 w2 _t1 _t2 LP IHL RP IHP L1 L2 L3 L4 E
       ].
  - rewrite Nat.add_1_r. apply le_S. apply L.
  - rewrite Nat.add_1_r. apply le_n_S. apply L.
  - apply IHP.
  - apply IHP.
Qed.


Theorem in_vs_inside : forall {vt nt} r i j w t
  (g : @Grammar vt nt) (H: @item vt nt g r i j w t),
    costs g (in_span i j) <= w + costs g (inf' g r).
Proof.
  intros vt nt r i j w t g.
  intros eta.
  induction eta
    as [ g r' i' I L
       | g r1 r2 i' j' v w' _t' P IHP L E1 E2
       | g l r' l' i' j' k w1 w2 _t1 _t2 LP IHL RP IHP L E
       | g l r l' i j k v w1 w2 _t1 _t2 LP IHL RP IHP L1 L2 L3 L4 E
       ].
  - simpl. rewrite in_span_ii_empty.
    unfold costs. simpl. apply le_0_n.
  - rewrite in_span_Sj.
    Focus 2. apply (item_i_le_j r1 i' j' w' _t' g). apply P.
    rewrite (shift_term_inf g r1 r2 v j').
    + rewrite costs_app. rewrite costs_app.
      rewrite plus_assoc.
      apply (plus_le_r _ _ (costs g [j'])).
      apply IHP.
    + apply E1.
    + apply E2.
  - rewrite (in_span_split i' j' k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.
    apply shift_inf in E as E'.
    rewrite <- E'. rewrite costs_app.
    rewrite (plus_assoc (w1 + w2)).
    rewrite (plus_assoc_reverse w1).
    rewrite (plus_comm w2).
    rewrite (plus_assoc).
    rewrite (plus_assoc_reverse (w1 + costs g (inf' g l))).
    apply (combine_le _ (w1 + costs g (inf' g l))).
    + apply IHL.
    + apply shift_inf_passive in L as L'.
      rewrite <- L'. apply IHP.
  - rewrite (in_span_split i j k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.
    rewrite plus_comm.
    rewrite (plus_comm w1).
    rewrite (plus_assoc_reverse w2).
    rewrite (plus_comm w1).
    rewrite (plus_assoc).
    rewrite (plus_assoc_reverse (w2 + omega g (fst r) (fst l))).
    apply (combine_le _ (w2 + omega g (fst r) (fst l))).
    + transitivity (w2 + costs g (inf' g r)).
      * apply IHP.
      * rewrite (plus_comm w2). rewrite (plus_comm w2).
        apply plus_le_r.
        apply (inf_cost_vs_omega' g r (fst l)).
        { apply L1. } { apply L2. }
    + apply root_non_term in L2 as L2'.
      destruct L2' as [x L2'].
      apply (shift_non_term_leaf_inf _ _ _ _ x) in L3 as [L5 L6].
      * rewrite L6. apply IHL.
      * apply L4.
      * rewrite L2' in E. apply E.
Qed.


Theorem in_vs_inside_root : forall {vt nt} r v i j w t
  (g : @Grammar vt nt) (H: @item vt nt g r i j w t),
    root g (fst r) = true ->
    shift g r = None ->
      costs g (in_span i j) <= w + omega g (fst r) v.
Proof.
  intros vt nt r v i j w t g I R N.
  transitivity (w + costs g (inf' g r)).
  - apply (in_vs_inside _ _ _ _ t). apply I.
  - apply combine_le. { reflexivity. }
    apply (inf_root_anchor) in R as A.
    apply shift_inf_passive in N as E.
    rewrite <- E in A.
    rewrite A.
    unfold costs. simpl.
    unfold omega.
    unfold cost.
    apply combine_le.
    + apply min_arc_weight_le.
    + apply min_tree_weight_le. reflexivity.
Qed.


Theorem monotonic : forall {vt nt} r i j w t
  (g : @Grammar vt nt) (H: @item vt nt g r i j w t),
    t <= w + heuristic g r i j.
Proof.
  intros vt nt r i j w t g.
  intros eta.

  destruct eta
    as [ g r' i' I L
       | g r1 r2 i' j' v w' _t' P L E1 E2
       | g l r' l' i' j' k w1 w2 _t1 _t2 LP RP L E
       | g l r l' i j k v w1 w2 _t1 _t2 LP RP L1 L2 L3 L4 E
       ].

  - (* AX *)
    simpl. apply le_0_n.

  - (* SC *)
    unfold total.
    rewrite (plus_comm w'). rewrite (plus_comm w').
    apply plus_le_r.
    unfold heuristic.
    apply shift_amort_weight in E1 as E1'.
    rewrite E1'.
    rewrite <- plus_assoc.
    apply combine_le. reflexivity.
    apply (item_i_le_j r1 i' j' w') in P as P'.
    apply (cost_rest_Sj g i') in L.
    rewrite L.
    apply term_inf in E2. rewrite E2.
    rewrite plus_comm.
    apply combine_le.
    reflexivity.
    reflexivity.

  - (* PS *)
    apply Nat.max_lub_iff. split.

    + unfold total.
      rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      unfold heuristic.
      apply shift_amort_weight in E as E'.
      rewrite E'.
      rewrite <- plus_assoc. rewrite (plus_comm w2).
      rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      rewrite (cost_rest_plus_in_r g i' j' k).
      * rewrite (plus_comm _ (costs g (rest g i' k))).
        rewrite <- plus_assoc.
        apply combine_le. { reflexivity. }
        rewrite <- shift_inf_passive.
        Focus 2. apply L.
        rewrite plus_comm.
        apply (in_vs_inside r' j' k w2 _t2).
        apply RP.
      * apply item_i_le_j in RP. apply RP.
      * apply item_j_le_term_max in RP. apply RP.

    + unfold total.
      rewrite (plus_comm w1).
      rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      unfold heuristic.
      rewrite (cost_rest_plus_in_l g i' j' k).
        Focus 2. apply item_i_le_j in LP. apply LP.

      rewrite plus_assoc. rewrite plus_assoc.
      apply combine_le. Focus 2. reflexivity.

      rewrite (plus_comm w1).
      apply (plus_le_l _ _ (costs g (inf' g l))).
      rewrite <- (plus_assoc _ w1).
      rewrite (plus_comm (amort_weight' g r')).
      rewrite (plus_comm (amort_weight' g l')).
      rewrite <- (plus_assoc).
      apply combine_le.
      * apply (in_vs_inside l _ _ _ _t1). apply LP.
      * apply amort_weight_complete in L as L'.
        rewrite <- L'.
        apply shift_amort_weight' in E as E'.
        rewrite E'. reflexivity.

  - (* SU *)

    apply root_non_term in L2 as H.
    destruct H as [x RNonTerm].
    apply (shift_non_term_leaf_inf g l l' v x) in L3 as H.
    destruct H as [InfVEmpty InfLEq].
    Focus 2. apply L4.
    Focus 2. rewrite RNonTerm in E. apply E.

    apply Nat.max_lub_iff. split.

    + unfold total.
      rewrite <- plus_assoc. rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      unfold heuristic.
      apply shift_amort_weight in L3 as L5.
      rewrite L5.

      (* [costs g (inf g v)] is 0 because v is a non-terminal leaf *)
      rewrite InfVEmpty. rewrite costs_nil.
      rewrite <- plus_n_O.

      (* get rid of [amort_weight' g l] on both sides *)
      rewrite (plus_comm w2).
      rewrite (plus_comm (omega _ _ _)).
      rewrite <- plus_assoc. rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }

      rewrite (cost_rest_plus_in_r g i j k).
      * apply combine_le. { reflexivity. }
        rewrite plus_comm.
        apply (in_vs_inside_root _ _ _ _ _ _t2).
        Focus 2. apply L2. Focus 2. apply L1.
        apply RP.
      * apply item_i_le_j in RP. apply RP.
      * apply item_j_le_term_max in RP. apply RP.

    + unfold total.

      rewrite (plus_comm w1).
      rewrite <- plus_assoc. rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }

      unfold heuristic.

      rewrite (cost_rest_plus_in_l g i j k).
        Focus 2. apply item_i_le_j in LP. apply LP.

      rewrite plus_assoc. rewrite plus_assoc. rewrite plus_assoc.
      apply combine_le. Focus 2. reflexivity.

      rewrite plus_comm.
      apply (plus_le_l _ _ (costs g (inf' g l))).
      rewrite <- plus_assoc.

      (* put everything in the right order *)
      rewrite <- plus_assoc.
      rewrite (plus_comm (amort_weight' g l')).
      rewrite (plus_assoc (w1 + omega g (fst r) (fst l))).
      rewrite <- (plus_assoc w1).
      rewrite (plus_comm (omega _ _ _)).
      rewrite (plus_assoc w1).
      rewrite <- plus_assoc.

      apply combine_le.
      * apply (in_vs_inside l _ _ _ _t1). apply LP.
      * apply combine_le.
        { unfold amort_weight'. unfold omega.
          rewrite (plus_comm (arc_weight _ _ _)).
          apply sup'_root in L2 as Rnil.
          Focus 2. apply L1.
          rewrite Rnil.
          assert (C0: costs g [] = 0).
            { unfold costs. simpl. reflexivity. }
          rewrite C0. rewrite <- minus_n_O.
          apply combine_le. { reflexivity. }
          apply min_arc_weight_le. }
        { apply shift_amort_weight' in L3 as E'.
          rewrite <- E'. rewrite plus_comm.
          assert (H: forall x y, x <= x + y).
            { intros a b. rewrite (plus_n_O a).
              apply combine_le.
              - rewrite <- plus_n_O. reflexivity.
              - apply le_0_n. }
          apply H. }

Qed.



