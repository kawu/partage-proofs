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


(** Parsing configuration *)
Inductive spot {vt} : Type :=
  | Node (v : vt)
  | Rule (r : vt*nat).


(** Value of the heuristic for the given passive item *)
Definition heuristic {vt nt}
  (g : @Grammar vt nt) (v : vt) (i j : term) : weight :=
    amort_weight g v + costs g (rest g i j).


(** Value of the heuristic for the given active item *)
Definition heuristic' {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term) : weight :=
    amort_weight' g r + costs g (rest g i j).


(** Inferior terminals for the given spot **)
Definition heuristic_s {vt nt}
  (g : @Grammar vt nt) (s : spot) (i j : term) : weight :=
    match s with
    | Node v => heuristic g v i j
    | Rule r => heuristic' g r i j
    end.


(** Active item's total weight: the inside weight +
    the heuristic estimation
**)
Definition total {vt nt}
  (g : @Grammar vt nt) (v : vt) (i j : term)
  (w : weight) (* inside weight *)
  : weight :=
    w + heuristic g v i j.


(** Active item's total weight: the inside weight +
    the heuristic estimation
**)
Definition total' {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term)
  (w : weight) (* inside weight *)
  : weight :=
    w + heuristic' g r i j.


(** Inferior terminals for the given spot **)
Definition inf_s {vt nt} (g : @Grammar vt nt) (s : spot) : list term :=
  match s with
  | Node v => inf g v
  | Rule r => inf' g r
  end.


(** Inference rules for chart items.

We thread the previous max total weight through the inference rules
in order to be able to easily check the monotonicity of the system.

*)
Inductive item {vt nt}
   : @Grammar vt nt
    (* the underlying grammar *)
  -> @spot vt -> term -> term
    (* spot, starting position, ending position *)
  -> weight
    (* inside weight *)
  -> weight
    (* previous max total weight *)
  -> Prop :=
  | axiom (g : @Grammar vt nt) (r : vt*nat) (i : term)
      (I: In r (rules g))
      (L: i <= term_max g) :
        item g (Rule r) i i 0 0
  | scan (g : @Grammar vt nt)
      (r r' : vt*nat) (i : term) (j : term) (v : vt) (w _t : weight)
      (P: item g (Rule r) i j w _t)
      (L: j <= term_max g)
      (Sh: shift g r = Some (v, r'))
      (Lb: label g v = Terminal j) :
        item g (Rule r') i (S j) w
          (total' g r i j w)
  | deact (g : @Grammar vt nt)
      (r : vt*nat) (v : vt) (i j : term) (w _t : weight)
      (P: item g (Rule r) i j w _t)
      (Sh: shift g r = None) :
        item g (Node (fst r)) i j w
          (total' g r i j w)
  | pseudo_subst (g : @Grammar vt nt)
      (l l' : vt*nat) (v : vt) (i j k : term) (w1 w2 _t1 _t2 : weight)
      (LP: item g (Rule l) i j w1 _t1)
      (RP: item g (Node v) j k w2 _t2)
      (Sh: shift g l = Some (v, l')) :
        item g (Rule l') i k (w1 + w2)
          (max (total' g l i j w1) (total g v j k w2))
  | subst (g : @Grammar vt nt)
      (l l' : vt*nat) (v v' : vt) (i j k : term) (w1 w2 _t1 _t2 : weight)
      (LP: item g (Rule l) i j w1 _t1)
      (RP: item g (Node v) j k w2 _t2)
      (Rv: root g v = true)
      (Le: leaf g v' = true)
      (Lb: label g v = label g v')
      (Sh: shift g l = Some (v', l')) :
        item g (Rule l') i k (w1 + w2 + omega g v (fst l))
          (max (total' g l i j w1) (total g v j k w2)).


Theorem item_i_le_j : forall {vt nt} s i j w t (g : @Grammar vt nt)
  (H: @item vt nt g s i j w t),
    i <= j.
Proof.
  intros vt nt s i j w t g.
  intros eta.
  induction eta
    as [ g r i I L
       | g r1 r2 i j v w _t P IHP L Sh Lb
       | g r v i j w _t P IHP Sh
       | g l l' v i j k w1 w2 _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k w1 w2 _t1 _t2 LP IHL RP IHP Rv Le Lb Sh
       ].
  - reflexivity.
  - apply le_S. apply IHP.
  - apply IHP.
  - transitivity j. { apply IHL. } { apply IHP. }
  - transitivity j. { apply IHL. } { apply IHP. }
Qed.


Theorem item_j_le_term_max : forall {vt nt} s i j w t (g : @Grammar vt nt)
  (H: @item vt nt g s i j w t),
    j <= term_max g + 1.
Proof.
  intros vt nt s i j w t g.
  intros eta.
  induction eta
    as [ g r i I L
       | g r1 r2 i j v w _t P IHP L Sh Lb
       | g r v i j w _t P IHP Sh
       | g l l' v i j k w1 w2 _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k w1 w2 _t1 _t2 LP IHL RP IHP Rv Le Lb Sh
       ].
  - rewrite Nat.add_1_r. apply le_S. apply L.
  - rewrite Nat.add_1_r. apply le_n_S. apply L.
  - apply IHP.
  - apply IHP.
  - apply IHP.
Qed.


Theorem in_vs_inside : forall {vt nt} s i j w t
  (g : @Grammar vt nt) (H: @item vt nt g s i j w t),
    costs g (in_span i j) <= w + costs g (inf_s g s).
Proof.
  intros vt nt s i j w t g.
  intros eta.
  induction eta
    as [ g r i I L
       | g r1 r2 i j v w _t P IHP L Sh Lb
       | g r v i j w _t P IHP Sh
       | g l l' v i j k w1 w2 _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k w1 w2 _t1 _t2 LP IHL RP IHP Rv Le Lb Sh
       ].
  - simpl. rewrite in_span_ii_empty.
    unfold costs. simpl. apply le_0_n.
  - rewrite in_span_Sj.
    Focus 2. apply (item_i_le_j (Rule r1) i j w _t g). apply P.
    simpl. rewrite (shift_term_inf g r1 r2 v j).
    + rewrite costs_app. rewrite costs_app.
      rewrite plus_assoc.
      apply (plus_le_r _ _ (costs g [j])).
      apply IHP.
    + apply Sh.
    + apply Lb.
  - simpl. simpl in IHP.
    apply shift_inf_passive in Sh as H.
    rewrite <- H.
    apply IHP.
  - rewrite (in_span_split i j k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.
    apply shift_inf in Sh as E.
    simpl.
    rewrite <- E. rewrite costs_app.
    rewrite (plus_assoc (w1 + w2)).
    rewrite (plus_assoc_reverse w1).
    rewrite (plus_comm w2).
    rewrite (plus_assoc).
    rewrite (plus_assoc_reverse (w1 + costs g (inf' g l))).
    apply (combine_le _ (w1 + costs g (inf' g l))).
    + apply IHL.
    + simpl in IHP. apply IHP.
  - rewrite (in_span_split i j k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.
    rewrite plus_comm.
    rewrite (plus_comm w1).
    rewrite (plus_assoc_reverse w2).
    rewrite (plus_comm w1).
    rewrite (plus_assoc).
    rewrite (plus_assoc_reverse (w2 + _)).
    apply (combine_le _ (w2 + _)).
    + transitivity (w2 + costs g (inf g v)).
      * simpl in IHP. apply IHP.
      * rewrite (plus_comm w2). rewrite (plus_comm w2).
        apply plus_le_r.
        apply (inf_cost_vs_omega g v (fst l)).
        apply Rv.
    + apply root_non_term in Rv as Rv'.
      destruct Rv' as [x Rv'].
      apply (shift_non_term_leaf_inf _ _ _ _ x) in Sh as [Sh1 Sh2].
      * simpl. rewrite Sh2. apply IHL.
      * apply Le.
      * rewrite Lb in Rv'. apply Rv'.
Qed.


Theorem in_vs_inside_root : forall {vt nt} v v' i j w t
  (g : @Grammar vt nt) (H: @item vt nt g (Node v) i j w t),
    root g v = true ->
      costs g (in_span i j) <= w + omega g v v'.
Proof.
  intros vt nt v v' i j w t g I R.
  transitivity (w + costs g (inf g v)).
  - assert (H: inf_s g (Node v) = inf g v).
      { simpl. reflexivity. }
    rewrite <- H. apply (in_vs_inside _ _ _ _ t). apply I.
  - apply combine_le. { reflexivity. }
    apply (inf_root_anchor) in R as A.
    rewrite A.
    unfold costs. simpl.
    unfold omega.
    unfold cost.
    apply combine_le.
    + apply min_arc_weight_le.
    + apply min_tree_weight_le. reflexivity.
Qed.


Theorem monotonic : forall {vt nt} s i j w t
  (g : @Grammar vt nt) (H: @item vt nt g s i j w t),
    t <= w + heuristic_s g s i j.
Proof.
  intros vt nt s i j w t g.
  intros eta.

  destruct eta
    as [ g r i I L
       | g r1 r2 i j v w _t P L Sh Lb
       | g r v i j w _t P Sh
       | g l l' v i j k w1 w2 _t1 _t2 LP RP Sh
       | g l l' v v' i j k w1 w2 _t1 _t2 LP RP Rv Le Lb Sh
       ].

  - (* AX *)
    simpl. apply le_0_n.

  - (* SC *)
    unfold total'.
    rewrite (plus_comm w). rewrite (plus_comm w).
    apply plus_le_r.
    simpl. unfold heuristic'.
    apply shift_amort_weight in Sh as Sh'. rewrite Sh'.
    rewrite <- plus_assoc.
    apply combine_le. reflexivity.
    apply (cost_rest_Sj g i) in L.
    rewrite L.
    apply term_inf in Lb. rewrite Lb.
    rewrite plus_comm.
    apply combine_le.
    reflexivity.
    reflexivity.

  - (* DE *)
    simpl. unfold total'.
    unfold heuristic. unfold heuristic'.
    unfold amort_weight. unfold amort_weight'.
    apply shift_sup_passive in Sh as H.
    rewrite <- H.
    reflexivity.

  - (* PS *)
    apply Nat.max_lub_iff. split.

    + simpl. unfold total'.
      rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      unfold heuristic'.
      apply shift_amort_weight in Sh as Sh'. rewrite Sh'.
      rewrite <- plus_assoc. rewrite (plus_comm w2).
      rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      rewrite (cost_rest_plus_in_r g i j k).
      * rewrite (plus_comm _ (costs g (rest g i k))).
        rewrite <- plus_assoc.
        apply combine_le. { reflexivity. }
        rewrite plus_comm.
        assert (H: inf_s g (Node v) = inf g v).
          { simpl. reflexivity. }
        rewrite <- H.
        apply (in_vs_inside (Node v) j k w2 _t2).
        apply RP.
      * apply item_i_le_j in RP. apply RP.
      * apply item_j_le_term_max in RP. apply RP.

    + unfold total. simpl.
      rewrite (plus_comm w1).
      rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      unfold heuristic. unfold heuristic'.
      rewrite (cost_rest_plus_in_l g i j k).
        Focus 2. apply item_i_le_j in LP. apply LP.

      rewrite plus_assoc. rewrite plus_assoc.
      apply combine_le. Focus 2. reflexivity.

      rewrite (plus_comm w1).
      apply (plus_le_l _ _ (costs g (inf' g l))).
      rewrite <- (plus_assoc _ w1).
      rewrite (plus_comm (amort_weight g v)).
      rewrite (plus_comm (amort_weight' g l')).
      rewrite <- (plus_assoc).
      apply combine_le.
      * assert (H: inf_s g (Rule l) = inf' g l).
          { simpl. reflexivity. }
        rewrite <- H.
        apply (in_vs_inside _ _ _ _ _t1). apply LP.
      * (* apply amort_weight_complete in L as L'.
        rewrite <- L'. *)
        apply shift_amort_weight' in Sh as Sh'.
        rewrite Sh'. reflexivity.

  - (* SU *)

    apply root_non_term in Rv as H.
    destruct H as [x RNonTerm].
    apply (shift_non_term_leaf_inf _ _ _ _ x) in Sh as H.
    destruct H as [InfVEmpty InfLEq].
    Focus 2. apply Le.
    Focus 2. rewrite RNonTerm in Lb. rewrite Lb. reflexivity.

    apply Nat.max_lub_iff. split.

    + unfold total'.
      rewrite <- plus_assoc. rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }
      simpl. unfold heuristic'.
      apply shift_amort_weight in Sh as Sh'. rewrite Sh'.

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
        Focus 2. apply Rv. (* Focus 2. apply L1. *)
        apply RP.
      * apply item_i_le_j in RP. apply RP.
      * apply item_j_le_term_max in RP. apply RP.

    + unfold total.

      rewrite (plus_comm w1).
      rewrite <- plus_assoc. rewrite <- plus_assoc.
      apply combine_le. { reflexivity. }

      simpl. unfold heuristic. unfold heuristic'.

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
      rewrite (plus_assoc (w1 + omega g v (fst l))).
      rewrite <- (plus_assoc w1).
      rewrite (plus_comm (omega _ _ _)).
      rewrite (plus_assoc w1).
      rewrite <- plus_assoc.

      apply combine_le.
      * assert (H: inf_s g (Rule l) = inf' g l).
          { simpl. reflexivity. }
        rewrite <- H.
        apply (in_vs_inside _ _ _ _ _t1). apply LP.
      * apply combine_le.
        { unfold amort_weight. unfold omega.
          rewrite (plus_comm (arc_weight _ _ _)).
          apply sup_root in Rv as Rnil.
          (* Focus 2. apply L1. *)
          rewrite Rnil.
          (* assert (C0: costs g [] = 0).
            { unfold costs. simpl. reflexivity. } *)
          rewrite costs_nil. rewrite <- minus_n_O.
          apply combine_le. { reflexivity. }
          apply min_arc_weight_le. }
        { apply shift_amort_weight' in Sh as E.
          rewrite <- E. rewrite plus_comm.
          assert (H: forall x y, x <= x + y).
            { intros a b. rewrite (plus_n_O a).
              apply combine_le.
              - rewrite <- plus_n_O. reflexivity.
              - apply le_0_n. }
          apply H. }

Qed.



