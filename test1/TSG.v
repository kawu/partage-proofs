From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

From LF Require Import Utils.
From LF Require Import LE.
From LF Require Import App.

(** Terminal (position) in the input sentence *)
Definition term := nat.

Inductive symbol {nt t} : Type :=
  | NonTerm (x : nt)
  | Terminal (x : t).

(* Weight; eventually should be represented by a real number? *)
Definition weight := nat.

(** Grammar representation.

The grammar must satisfy certain additional constraints, not encoded
in the representation below.  For example:
* The set of terminals in [rule_set] is the same as in [term_set].
* The set of terminals [term_set] is indeed a set (even though
  it is represented by a list).
* The set of dotted rules [dotted_set] directly steps from [rule_set].

We also don't care what are the values of the functions such as [label],
[root], or [tree_weight] for the arguments outside of the underlying
domains.

The fact that we do not directly encode these constraints should
not be a problem.  If we manage to prove a property for the
grammars in general, it should also hold for a grammar with all
the well-formedness constraints satisfied.

*)
Record Grammar {vert non_term : Type} := mkGram
  { vertices : list vert
      (* the list (=>set) of vertices in the grammar *)
  ; terminals : list term
      (* the list (=>set) of terminals in the grammar *)

  ; term_max : term
      (* the last position in the sentence *)
  ; term_max_correct : maximum terminals = Some term_max
  ; term_min_correct : minimum terminals = Some 0

  ; root : vert -> bool
      (* is the given node a root of an ET? *)
  ; leaf : vert -> bool
      (* is the given node a leaf of an ET? *)
  ; anchor : vert -> term
      (* anchor terminal of the ET containing the given node *)
  ; label : vert -> @symbol non_term term
      (* node labeling function (either non-terminal or terminal
         is assigned to each vertex) *)

  ; root_has_non_term : forall v,
      root v = true ->
        exists x, label v = NonTerm x
      (* label assigned to a root is a non-terminal *)

  ; parent : vert -> option vert
      (* parent of the given vertex (root => None) *)
  ; children : vert -> list vert
      (* the list of children of the given vertex (leaf => nil) *)

  ; inf : vert -> list term
      (* the list (=>set) of terminals under and in the given node. *)
  ; sup : vert -> list term
      (* the list (=>set) of terminals over the given node. *)
  ; inf_plus_sup :
      forall n : vert,
        inf n ++ sup n = [anchor n]
      (* We assume that there is a single anchor in each ET;
         hence, the set of inferior plus the set of superior
         nodes will always contain this unique anchor. *)

  ; inf_root_anchor : forall v,
      root v = true ->
        inf v = [anchor v]
      (* [inf] of the grammar root contains its single anchor terminal *)

  ; inf' : vert * nat -> list term
      (* the list (=>set) of the processed terminals after
         traversing (at most) the give number of children,
         from left to right. *)
  ; sup' : vert * nat -> list term
      (* the list (=>set) of the terminals remaining to match after
         traversing (at most) the give number of children,
         from left to right. *)
  ; inf_plus_sup' :
      forall (r : vert * nat),
        inf' r ++ sup' r = [anchor (fst r)]

  ; tree_weight : vert -> weight
      (* weight of the ET containing the given node *)
  ; arc_weight : term -> term -> weight
      (* weight of the given (dependency, head) arc *)

  ; min_tree_weight : term -> weight
      (* minimal ET weight for the given terminal *)
  ; min_arc_weight : term -> weight
      (* minimal dependency weight for the given dependent *)

  ; min_tree_weight_leb :
      forall (v : vert) (t : term),
        anchor v = t ->
          min_tree_weight t <= tree_weight v
      (* minimal ET weight smaller than others *)
  ; min_arc_weight_leb :
      forall (dep hed : term),
        min_arc_weight dep <= arc_weight dep hed
      (* minimal ET weight smaller than others *)

  ; shift : vert * nat -> option (vert * (vert * nat))
      (* shift the dot *)

  (* various shift-related properties (and more) *)
  ; shift_preserves_head : forall r r' v,
      shift r = Some (v, r') ->
        fst r = fst r'
  ; shift_inf : forall r r' v,
      shift r = Some (v, r') ->
        inf' r ++ inf v = inf' r'
  ; shift_inf_passive : forall r,
      shift r = None ->
        inf' r = inf (fst r)

  ; shift_term_inf : forall r r' v i,
      shift r = Some (v, r') ->
      label v = Terminal i ->
        inf' r' = inf' r ++ [i]
  ; shift_non_term_leaf_inf : forall r r' v x,
      shift r = Some (v, r') ->
      leaf v = true ->
      label v = NonTerm x ->
        inf v = [] /\ inf' r' = inf' r
  ; no_shift_inf : forall r,
      shift r = None ->
        inf' r = inf (fst r)
  ; term_inf : forall v i,
      label v = Terminal i ->
        inf v = [i]

  ; shift_preserves_tree_weight : forall l v l',
      shift l = Some (v, l') ->
        tree_weight v = tree_weight (fst l')
  ; shift_preserves_anchor : forall l v l',
      shift l = Some (v, l') ->
        anchor v = anchor (fst l')
  }.


Lemma inf'_tail_empty : forall {vt nt}
  (g : @Grammar vt nt) (r : vt * nat) x l,
    inf' g r = x :: l ->
      l = [].
Proof.
  intros vt nt g r x l.
  intros H.
  destruct (inf' g r) as [|x' l'] eqn:E.
  - discriminate H.
  - injection H as H1 H2.
    apply (app_pref_eq_r' _ _ (sup' g r)) in E.
    rewrite inf_plus_sup' in E.
    simpl in E. injection E as E.
    rewrite H2 in H.
    destruct l as [|h t] eqn:E'.
    + reflexivity.
    + simpl in H. discriminate H.
Qed.

Lemma shift_one_empty :  forall {vt nt}
  (g : @Grammar vt nt) (r r' : vt * nat) v,
      shift g r = Some (v, r') ->
        inf g v = [] \/ inf' g r = [].
Proof.

  intros vt nt g r r' v.
  intros H1.
  apply shift_inf in H1 as H2.
  destruct (inf' g r') as [|h t] eqn:E1.

  - destruct (inf' g r) as [|h' t'] eqn:E2.
    + right. reflexivity.
    + simpl in H2. discriminate H2.

  - apply inf'_tail_empty in E1 as E2.
    rewrite E2 in E1. rewrite E2 in H2.

    destruct (inf' g r) as [|h' t'] eqn:E3.
      + right. reflexivity.
      + simpl in H2.
        injection H2 as H3 H4.

        destruct t'.
        * simpl in H4. left. apply H4.
        * simpl in H4.  discriminate H4.
Qed.

Lemma shift_inf' :  forall {vt nt}
  (g : @Grammar vt nt) (r r' : vt * nat) v,
      shift g r = Some (v, r') ->
        inf g v ++ inf' g r = inf' g r'.
Proof.
  intros vt nt g r r' v H.

  destruct (inf' g r) as [|h t] eqn:E1.

  * rewrite <- E1.
    rewrite <- (shift_inf g r r' v).
    Focus 2. apply H.
    destruct (inf' g r) as [|h t] eqn:E2.
    - simpl. rewrite app_nil_r. reflexivity.
    - discriminate E1.

  * rewrite <- (shift_inf g r r' v).
    Focus 2. apply H.
    rewrite E1.

    destruct (inf g v) as [|h' t'] eqn:E2.
    - simpl. rewrite app_nil_r. reflexivity.
    - apply shift_one_empty in H as [H1 | H2].
      + rewrite H1 in E2. discriminate E2.
      + rewrite H2 in E1. discriminate E1.

Qed.

Lemma shift_sup_passive :  forall {vt nt}
  (g : @Grammar vt nt) (r : vt * nat),
    shift g r = None ->
      sup' g r = sup g (fst r).
Proof.
  (* NOTE: maybe a simpler proof could be devised? *)
  intros vt nt g r. intros H1.
  apply shift_inf_passive in H1 as H2.
  apply (app_pref_eq_r' _ _ (sup' g r)) in H2 as H3.
  apply (app_pref_eq_r' _ _ (sup g (fst r))) in H2.
  rewrite inf_plus_sup in H2.
  rewrite inf_plus_sup' in H3.
  rewrite H3 in H2.
  apply shift_inf_passive in H1 as H4.
  rewrite H4 in H2.
  apply (app_pref_eq) in H2.
  rewrite H2. reflexivity.
Qed.

(** The list (=>set) of production rules in the grammar *)
Definition rules {vt nt} (g : @Grammar vt nt) : list (vt*nat) :=
  let
    f v :=
      if leaf g v
      then None
      else Some (v, 0)
  in
    map_maybe f (vertices g).

(** Weight of the given (dependent, head) arc +
    weight of the dependent ET
*)
Definition omega {vt nt}
    (g : @Grammar vt nt) (dep gov : vt) : weight :=
  arc_weight g (anchor g dep) (anchor g gov) +
  tree_weight g dep.

(** The minimal cost of scanning the given terminal *)
Definition cost {vt nt} (g : @Grammar vt nt) (t : term) : weight :=
  min_arc_weight g t + min_tree_weight g t.

(** The minimal cost of scanning the given list of terminals *)
Definition costs {vt nt}
    (g : @Grammar vt nt) (ts : list term) : weight :=
  fold_left plus (map (cost g) ts) 0.

Lemma head_inf_sup_eq : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt * nat),
  fst r' = fst r ->
    inf' g r' ++ sup' g r' = inf' g r ++ sup' g r.
Proof.
  intros vt nt g r r'. intros H.
  rewrite inf_plus_sup'.
  rewrite inf_plus_sup'.
  rewrite H. reflexivity.
Qed.

Lemma shift_sup : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r' = Some (v, r) ->
    sup' g r' = inf g v ++ sup' g r.
Proof.
  intros vt nt g r r' w H.
  destruct (shift g r') as [r''|] eqn:E.
  - apply app_pref_eq with (pref := inf' g r').
    rewrite app_assoc.
    rewrite shift_inf with (r'0 := r).
    + apply head_inf_sup_eq.
      apply shift_preserves_head with (g0 := g) (v := w).
      rewrite E. apply H.
    + rewrite E. apply H.
  - discriminate H.
Qed.

Lemma shift_sup' : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r' = Some (v, r) ->
    sup g v = inf' g r' ++ sup' g r.
Proof.
  intros vt nt g r r' v H.
  destruct (shift g r') as [r''|] eqn:E.
  - apply app_pref_eq with (pref := inf g v).
    rewrite app_assoc. rewrite H in E.
    apply shift_inf' in E as E1.
    rewrite E1.
    rewrite inf_plus_sup.
    rewrite inf_plus_sup'.
    apply shift_preserves_anchor in E as E2.
    rewrite E2. reflexivity.
  - discriminate H.
Qed.

Lemma fold_left_plus : forall (x : nat) (l : list nat),
  fold_left plus l x = fold_left plus l 0 + x.
Proof.
  intros x l.
  generalize dependent x.
  induction l as [|h t IH].
  - intros x. simpl. reflexivity.
  - intros x. simpl. rewrite IH.
    rewrite (IH h). rewrite <- plus_assoc.
    rewrite (plus_comm x h). reflexivity.
Qed.

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

(** Amortized weight of the given parsing configuration *)
Definition amort_weight {vt nt} (g : @Grammar vt nt) (n : vt) : weight :=
  tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup g n).

(** Amortized weight of the given parsing configuration *)
Definition amort_weight' {vt nt} (g : @Grammar vt nt) (r : vt*nat) : weight :=
  let n := fst r
  in tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup' g r).

Lemma sup_destr : forall {vt nt}
  (g : @Grammar vt nt) (v : vt) (x : nat) (l : list nat),
    sup g v = x :: l ->
      x = anchor g v /\ l = [].
Proof.
  intros vt nt g v x l.
  intros H.
  apply (app_pref_eq' _ _ (inf g v)) in H as H'.
  rewrite inf_plus_sup in H'.
  destruct (inf g v) eqn:E.
  - simpl in H'.
    inversion H'.
    split.
    + reflexivity.
    + reflexivity.
  - inversion H'.
    destruct l0 eqn:E'.
    + simpl in H2. discriminate H2.
    + simpl in H2. discriminate H2.
Qed.

Lemma sup'_destr : forall {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (x : nat) (l : list nat),
    sup' g r = x :: l ->
      x = anchor g (fst r) /\ l = [].
Proof.
  intros vt nt g r x l.
  intros H.
  apply (app_pref_eq' _ _ (inf' g r)) in H as H'.
  rewrite inf_plus_sup' in H'.
  destruct (inf' g r) eqn:E.
  - simpl in H'.
    inversion H'.
    split.
    + reflexivity.
    + reflexivity.
  - inversion H'.
    destruct l0 eqn:E'.
    + simpl in H2. discriminate H2.
    + simpl in H2. discriminate H2.
Qed.

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

(*
Lemma shift_cost_sup' : forall {vt nt}
  (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
    shift g r' = Some (v, r) ->
      costs g (sup g v) = costs g (inf' g r') + costs g (sup' g r).
*)

(** The list (=>set) of terminals inside the given span *)
Fixpoint in_span (i j : term) : list term :=
  match j with
  | 0 => []
  | S j' =>
    if i <=? j'
    then in_span i j' ++ [j']
    else []
  end.

Example in_span_ex1 : in_span 1 3 = [1; 2].
Proof. reflexivity. Qed.

Example in_span_ex2 : in_span 1 1 = [].
Proof. reflexivity. Qed.

Lemma not_S_i_leb_i : forall (i : term), (S i <=? i = false).
Proof.
  intros i.
  induction i as [|i' IH].
  - simpl. reflexivity.
  - simpl in IH. simpl. apply IH.
Qed.

Lemma in_span_ii_empty : forall (i : term),
  in_span i i = [].
Proof.
  intros i.
  unfold in_span.
  destruct i as [|i'].
  - reflexivity.
  - destruct (S i' <=? i') eqn:E.
    + rewrite not_S_i_leb_i in E. discriminate E.
    + reflexivity.
Qed.

Theorem in_span_Sj : forall i j : term,
  i <= j -> in_span i (S j) = in_span i j ++ [j].
Proof.
  intros i j H.
  simpl.
  destruct (lebP i j) as [H'|H'].
  - reflexivity.
  - apply H' in H. destruct H.
Qed.

Theorem in_span_Si : forall i j : term,
  S i <= j -> [i] ++ in_span (S i) j = in_span i j.
Proof.
  intros i j H.
  induction H.
  - simpl. destruct i as [|i'] eqn:E.
    + simpl. reflexivity.
    + rewrite not_S_i_leb_i.
      rewrite Nat.leb_refl.
      rewrite in_span_ii_empty.
      simpl. reflexivity.
  - rewrite in_span_Sj.
    Focus 2. apply H.
    rewrite in_span_Sj.
    + rewrite <- IHle. rewrite app_assoc. reflexivity.
    + transitivity (S i).
      * apply le_S. reflexivity.
      * apply H.
Qed.

Lemma in_span_split : forall i j k,
  i <= j ->
  j <= k ->
    in_span i k = in_span i j ++ in_span j k.
Proof.
  intros i j k H1 H2.
  generalize dependent j.
  generalize dependent i.
  induction k as [|k'].
  - intros i j.
    simpl.
    intros H1 H2.
    assert (H3: j = 0). { inversion H2. reflexivity. }
    assert (H4: i = 0). { rewrite H3 in H1. inversion H1. reflexivity. }
    rewrite H3. rewrite H4. rewrite in_span_ii_empty. simpl. reflexivity.
  - intros i j. intros H1 H2.
    inversion H2 as [H3|m H3 H4].
    + rewrite in_span_ii_empty. rewrite app_nil_r. reflexivity.
    + apply (leb_trans i j m) in H1 as H5.
      Focus 2. rewrite H4. apply H3.
      apply (in_span_Sj i m) in H5. rewrite H4 in H5.
      apply (in_span_Sj j k') in H3 as H6.
      rewrite H5. rewrite H6.
      rewrite app_assoc.
      apply app_suf_eq.
      apply IHk'.
      * apply H1.
      * apply H3.
Qed.

(** The list (=>set) of terminals outside of the given span *)
(** TODO: rename as [out] at some point *)
(** TODO: [term_max g] or [term_max g + 1]? *)
Definition rest {vt nt} (g : @Grammar vt nt) (i j : term) : list term :=
  in_span 0 i ++ in_span j (term_max g + 1).

(*
Lemma rest_Sj : forall {vt nt} (g : @Grammar vt nt) (i j : term),
  i <= j -> rest g i j = rest g i (S j) ++ [j].
Proof.
  intros vt nt g i j H.
  unfold rest.
  rewrite <- app_assoc.
  apply app_pref_eq'.
  simpl.
Admitted.
*)

Lemma cost_one : forall {vt nt} (g : @Grammar vt nt) (i : term),
  cost g i = costs g [i].
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
  - simpl. rewrite cost_one.
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

Definition heuristic {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term) : weight :=
    amort_weight' g r + costs g (rest g i j).

Definition total {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term) (w : weight) : weight :=
    w + heuristic g r i j.

(** Chart items and the rules to infer them. *)
Inductive item {vt nt} 
  : @Grammar vt nt
           -> vt*nat -> term -> term -> weight
           (* -> weight (* value of the heuristic *) *)
           -> weight (* previous max total value *)
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

Theorem item_i_leb_j : forall {vt nt} r i j w t (g : @Grammar vt nt)
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

Theorem item_j_leb_term_max : forall {vt nt} r i j w t (g : @Grammar vt nt)
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
    Focus 2. apply (item_i_leb_j r1 i' j' w' _t' g). apply P.
    rewrite (shift_term_inf g r1 r2 v j').
    + rewrite costs_app. rewrite costs_app.
      rewrite plus_assoc.
      apply (plus_leb_r _ _ (costs g [j'])).
      apply IHP.
    + apply E1.
    + apply E2.
  - rewrite (in_span_split i' j' k).
    Focus 2. apply item_i_leb_j in LP. apply LP.
    Focus 2. apply item_i_leb_j in RP. apply RP.
    rewrite costs_app.
    apply shift_inf in E as E'.
    rewrite <- E'. rewrite costs_app.
    rewrite (plus_assoc (w1 + w2)).
    rewrite (plus_assoc_reverse w1).
    rewrite (plus_comm w2).
    rewrite (plus_assoc).
    rewrite (plus_assoc_reverse (w1 + costs g (inf' g l))).
    apply (combine_leb _ (w1 + costs g (inf' g l))).
    + apply IHL.
    + apply shift_inf_passive in L as L'.
      rewrite <- L'. apply IHP.
  - rewrite (in_span_split i j k).
    Focus 2. apply item_i_leb_j in LP. apply LP.
    Focus 2. apply item_i_leb_j in RP. apply RP.
    rewrite costs_app.
    rewrite plus_comm.
    rewrite (plus_comm w1).
    rewrite (plus_assoc_reverse w2).
    rewrite (plus_comm w1).
    rewrite (plus_assoc).
    rewrite (plus_assoc_reverse (w2 + omega g (fst r) (fst l))).
    apply (combine_leb _ (w2 + omega g (fst r) (fst l))).
    + transitivity (w2 + costs g (inf' g r)).
      * apply IHP.
      * rewrite (plus_comm w2). rewrite (plus_comm w2).
        apply plus_leb_r.
        apply (inf_cost_vs_omega' g r (fst l)).
        { apply L1. } { apply L2. }
    + apply root_has_non_term in L2 as L2'.
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
  - apply combine_leb. { reflexivity. }
    apply (inf_root_anchor) in R as A.
    apply shift_inf_passive in N as E.
    rewrite <- E in A.
    rewrite A.
    unfold costs. simpl.
    unfold omega.
    unfold cost.
    apply combine_leb.
    + apply min_arc_weight_leb.
    + apply min_tree_weight_leb. reflexivity.
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

Lemma root_non_term : forall {vt nt}
  (g : @Grammar vt nt) v,
    root g v = true ->
      exists x, label g v = NonTerm x.
Proof.
Admitted.

Lemma costs_nil :  forall {vt nt}
  (g : @Grammar vt nt),
    costs g [] = 0.
Proof.
  intros vt nt g.
  unfold costs. simpl. reflexivity.
Qed.

Lemma sup'_root : forall {vt nt}
  (g : @Grammar vt nt) r,
    root g (fst r) = true ->
    shift g r = None ->
      sup' g r = [].
Proof.
Admitted.

Theorem monotonic : forall {vt nt} r i j w t
  (g : @Grammar vt nt) (H: @item vt nt g r i j w t),
    t <= w + heuristic g r i j.
Proof.
  intros vt nt r i j w t g.
  intros eta.
  (* TODO: don't really need to use induction here! *)
  induction eta
    as [ g r' i' I L
       | g r1 r2 i' j' v w' _t' P IHP L E1 E2
       | g l r' l' i' j' k w1 w2 _t1 _t2 LP IHL RP IHP L E
       | g l r l' i j k v w1 w2 _t1 _t2 LP IHL RP IHP L1 L2 L3 L4 E
       ].

  - (* AX *)
    simpl. apply le_0_n.

  - (* SC *)
    unfold total.
    rewrite (plus_comm w'). rewrite (plus_comm w').
    apply plus_leb_r.
    unfold heuristic.
    apply shift_amort_weight in E1 as E1'.
    rewrite E1'.
    rewrite <- plus_assoc.
    apply combine_leb. reflexivity.
    apply (item_i_leb_j r1 i' j' w') in P as P'.
    apply (cost_rest_Sj g i') in L.
    rewrite L.
    apply term_inf in E2. rewrite E2.
    rewrite plus_comm.
    apply combine_leb.
    reflexivity.
    reflexivity.

  - (* PS *)
    apply Nat.max_lub_iff. split.

    + unfold total.
      rewrite <- plus_assoc.
      apply combine_leb. { reflexivity. }
      unfold heuristic.
      apply shift_amort_weight in E as E'.
      rewrite E'.
      rewrite <- plus_assoc. rewrite (plus_comm w2).
      rewrite <- plus_assoc.
      apply combine_leb. { reflexivity. }
      rewrite (cost_rest_plus_in_r g i' j' k).
      * rewrite (plus_comm _ (costs g (rest g i' k))).
        rewrite <- plus_assoc.
        apply combine_leb. { reflexivity. }
        rewrite <- shift_inf_passive.
        Focus 2. apply L.
        rewrite plus_comm.
        apply (in_vs_inside r' j' k w2 _t2).
        apply RP.
      * apply item_i_leb_j in RP. apply RP.
      * apply item_j_leb_term_max in RP. apply RP.

    + unfold total.
      rewrite (plus_comm w1).
      rewrite <- plus_assoc.
      apply combine_leb. { reflexivity. }
      unfold heuristic.
      rewrite (cost_rest_plus_in_l g i' j' k).
        Focus 2. apply item_i_leb_j in LP. apply LP.

      rewrite plus_assoc. rewrite plus_assoc.
      apply combine_leb. Focus 2. reflexivity.

      rewrite (plus_comm w1).
      apply (plus_leb_l _ _ (costs g (inf' g l))).
      rewrite <- (plus_assoc _ w1).
      rewrite (plus_comm (amort_weight' g r')).
      rewrite (plus_comm (amort_weight' g l')).
      rewrite <- (plus_assoc).
      apply combine_leb.
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
      apply combine_leb. { reflexivity. }
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
      apply combine_leb. { reflexivity. }

      rewrite (cost_rest_plus_in_r g i j k).
      * apply combine_leb. { reflexivity. }
        rewrite plus_comm.
        apply (in_vs_inside_root _ _ _ _ _ _t2).
        Focus 2. apply L2. Focus 2. apply L1.
        apply RP.
      * apply item_i_leb_j in RP. apply RP.
      * apply item_j_leb_term_max in RP. apply RP.

    + unfold total.

      rewrite (plus_comm w1).
      rewrite <- plus_assoc. rewrite <- plus_assoc.
      apply combine_leb. { reflexivity. }

      unfold heuristic.

      rewrite (cost_rest_plus_in_l g i j k).
        Focus 2. apply item_i_leb_j in LP. apply LP.

      rewrite plus_assoc. rewrite plus_assoc. rewrite plus_assoc.
      apply combine_leb. Focus 2. reflexivity.

      rewrite plus_comm.
      apply (plus_leb_l _ _ (costs g (inf' g l))).
      rewrite <- plus_assoc.

      (* put everything in the right order *)
      rewrite <- plus_assoc.
      rewrite (plus_comm (amort_weight' g l')).
      rewrite (plus_assoc (w1 + omega g (fst r) (fst l))).
      rewrite <- (plus_assoc w1).
      rewrite (plus_comm (omega _ _ _)).
      rewrite (plus_assoc w1).
      rewrite <- plus_assoc.

      apply combine_leb.
      * apply (in_vs_inside l _ _ _ _t1). apply LP.
      * apply combine_leb.
        { unfold amort_weight'. unfold omega.
          rewrite (plus_comm (arc_weight _ _ _)).
          apply sup'_root in L2 as Rnil.
          Focus 2. apply L1.
          rewrite Rnil.
          assert (C0: costs g [] = 0).
            { unfold costs. simpl. reflexivity. }
          rewrite C0. rewrite <- minus_n_O.
          apply combine_leb. { reflexivity. }
          apply min_arc_weight_leb. }
        { apply shift_amort_weight' in L3 as E'.
          rewrite <- E'. rewrite plus_comm.
          assert (H: forall x y, x <= x + y).
            { intros a b. rewrite (plus_n_O a).
              apply combine_leb.
              - rewrite <- plus_n_O. reflexivity.
              - apply le_0_n. }
          apply H. }

Qed.





