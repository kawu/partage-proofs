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


(** The minimal cost of scanning the given terminal *)
Definition cost {vt nt} (g : @Grammar vt nt) (t : term) : weight :=
  min_arc_weight g t + min_tree_weight g t.


(** The minimal cost of scanning the given list of terminals *)
Definition costs {vt nt}
    (g : @Grammar vt nt) (ts : list term) : weight :=
  fold_left plus (map (cost g) ts) 0.


Lemma costs_app : forall {vt nt}
    (g : @Grammar vt nt) (ts ts' : list term),
  costs g (ts ++ ts') = costs g ts + costs g ts'.
Proof.
  intros vt nt g ts ts'.
  generalize dependent ts'.
  induction ts as [|tsh tst IH].
  - intros ts'. simpl. reflexivity.
  - intros ts'. rewrite <- app_comm_cons.
    unfold costs. simpl.
    unfold costs in IH.
    rewrite fold_left_plus. rewrite (fold_left_plus (cost g tsh)).
    rewrite IH. rewrite <- plus_assoc.
    rewrite (plus_comm _ (cost _ _)).
    rewrite plus_assoc. reflexivity.
Qed.


Lemma shift_cost_sup : forall {vt nt}
  (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
    shift g r' = Some (v, r) ->
      costs g (sup' g r') = costs g (inf g v) + costs g (sup' g r).
Proof.
  intros vt nt g r r' v H.
  destruct (shift g r') as [(v', r'')|] eqn:E.
  - rewrite shift_sup with (r0 := r) (v0 := v).
    + rewrite <- costs_app. apply f_equal. reflexivity.
    + rewrite <- H. apply E.
  - discriminate H.
Qed.


Lemma shift_cost_sup' : forall {vt nt}
  (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
    shift g r' = Some (v, r) ->
      costs g (sup g v) = costs g (inf' g r') + costs g (sup' g r).
Proof.
  intros vt nt g r r' v H.
  destruct (shift g r') as [(v', r'')|] eqn:E.
  - injection H as H1 H2.
    rewrite H1 in E. rewrite H2 in E.
    apply (shift_sup' g r r' v) in E as E'.
    rewrite E'.
    rewrite costs_app. reflexivity.
  - discriminate H.
Qed.


Lemma costs_nil :  forall {vt nt}
  (g : @Grammar vt nt),
    costs g [] = 0.
Proof.
  intros vt nt g.
  unfold costs. simpl. reflexivity.
Qed.


Lemma cost_one : forall {vt nt} (g : @Grammar vt nt) (i : term),
  costs g [i] = cost g i.
Proof.
  intros vt nt g i.
  unfold costs.
  simpl. reflexivity.
Qed.


(* TODO: prove based on cost_rest_plus_in_r *)
Lemma cost_rest_Sj : forall {vt nt} (g : @Grammar vt nt) (i j : term),
  j <= term_max g ->
    costs g (rest g i j) = costs g (rest g i (S j)) + cost g j.
Proof.
  intros vt nt g i j H2.
  unfold rest.
  rewrite costs_app.
  rewrite costs_app.
  rewrite <- plus_assoc.
  apply (f_equal2_plus). { reflexivity. }
  simpl.
  rewrite <- in_span_Si.
  - simpl. rewrite <- cost_one.
    rewrite (plus_comm _ (costs g [j])).
    rewrite <- costs_app.
    simpl. reflexivity.
  - rewrite plus_comm. simpl.
    apply le_n_S. apply H2.
Qed.


Lemma cost_rest_plus_in_r : forall {vt nt}
  (g : @Grammar vt nt) (i j k : term),
    j <= k ->
    k <= term_max g + 1 ->
      costs g (rest g i j) = costs g (rest g i k) + costs g (in_span j k).
Proof.
  intros vt nt g i j k H1 H2.
  unfold rest.
  rewrite costs_app. rewrite costs_app.
  rewrite <- plus_assoc.
  apply f_equal2_plus. { reflexivity. }
  rewrite (in_span_split j k).
  - rewrite costs_app. rewrite plus_comm. reflexivity.
  - apply H1.
  - apply H2.
Qed.

Lemma cost_rest_plus_in_l : forall {vt nt}
  (g : @Grammar vt nt) (i j k : term),
    i <= j ->
      costs g (rest g j k) = costs g (in_span i j) + costs g (rest g i k).
Proof.
  intros vt nt g i j k H1.
  unfold rest.
  rewrite costs_app.
  rewrite costs_app.
  rewrite plus_assoc.
  apply (f_equal2_plus).
  Focus 2. reflexivity.
  rewrite plus_comm.
  rewrite (in_span_split 0 i j).
  - rewrite costs_app. reflexivity.
  - apply le_0_n.
  - apply H1.
Qed.


Lemma inf_cost_vs_omega : forall {vt nt} (g : @Grammar vt nt) (v w : vt),
  root g v = true ->
    costs g (inf g v) <= omega g v w.
Proof.
  intros vt nt g v w.
  intros RH.
  unfold omega.
  apply inf_root_anchor in RH as H.
  rewrite H.
  unfold costs. simpl.
  unfold cost.
  apply (combine_leb).
  - apply min_arc_weight_leb.
  - apply min_tree_weight_leb. reflexivity.
Qed.


Lemma inf_cost_vs_omega' :
  forall {vt nt} (g : @Grammar vt nt) (r : vt*nat) (w : vt),
    shift g r = None ->
    root g (fst r) = true ->
      costs g (inf' g r) <= omega g (fst r) w.
Proof.
  intros vt nt g r w H.
  apply no_shift_inf in H as H'.
  rewrite H'.
  intros R.
  apply inf_cost_vs_omega.
  apply R.
Qed.

