From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

From LF Require Import Utils.
From LF Require Import App.

(** Terminal (position) in the input sentence *)
Definition term := nat.

Inductive symbol {nt t} : Type :=
  | NonTerm (x : nt)
  | Terminal (x : t).

(* Weight; eventually should be represented by a real number? *)
Definition weight := nat.

(** Grammar representation.

* [vert] -- type of vertex (node)
* [non_term] -- non-terminal type

Making the grammar [vert] polymorphic makes it safe to specify
the grammar in terms of total functions ([root], [leaf]).

Whatever we prove for this grammar representation should also hold
in the case where the vertex set is finite, since [vert] can be
in general instantiated with a simple, finite type.

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

  ; root_non_term : forall v,
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


(**
  Additional definitions
**)


(** Weight of the given (dependent, head) arc +
    weight of the dependent ET
*)
Definition omega {vt nt}
    (g : @Grammar vt nt) (dep gov : vt) : weight :=
  arc_weight g (anchor g dep) (anchor g gov) +
  tree_weight g dep.


(** The list (=>set) of production rules in the grammar *)
Definition rules {vt nt} (g : @Grammar vt nt) : list (vt*nat) :=
  let
    f v :=
      if leaf g v
      then None
      else Some (v, 0)
  in
    map_maybe f (vertices g).


(**
  Various additional properties stemming from the grammar representation
**)


(** [inf'] can contain at most one terminal *)
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


Lemma sup_root : forall {vt nt}
  (g : @Grammar vt nt) v,
    root g v = true ->
      sup g v = [].
Proof.
  intros vt nt g v H.
  apply (app_pref_eq _ _ (inf g v)).
  apply inf_root_anchor in H.
  rewrite inf_plus_sup.
  rewrite app_nil_r.
  rewrite <- H. reflexivity.
Qed.


Lemma sup'_root : forall {vt nt}
  (g : @Grammar vt nt) r,
    root g (fst r) = true ->
    shift g r = None ->
      sup' g r = [].
Proof.
  intros vt nt g r H1 H2.
  apply sup_root in H1.
  apply shift_sup_passive in H2.
  rewrite H1 in H2.
  apply H2.
Qed.