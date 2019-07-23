(** * Maps: Total and Partial Maps *)

(** _Maps_ (or _dictionaries_) are ubiquitous data structures both
    generally and in the theory of programming languages in
    particular; we're going to need them in many places in the coming
    chapters.  They also make a nice case study using ideas we've seen
    in previous chapters, including building data structures out of
    higher-order functions (from [Basics] and [Poly]) and the use of
    reflection to streamline proofs (from [IndProp]).

    We'll define two flavors of maps: _total_ maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist, and _partial_ maps, which return an [option] to
    indicate success or failure.  The latter is defined in terms of
    the former, using [None] as the default element. *)

(* ################################################################# *)
(** * The Coq Standard Library *)

(** One small digression before we begin...

    Unlike the chapters we have seen so far, this one does not
    [Require Import] the chapter before it (and, transitively, all the
    earlier chapters).  Instead, in this chapter and from now, on
    we're going to import the definitions and theorems we need
    directly from Coq's standard library stuff.  You should not notice
    much difference, though, because we've been careful to name our
    own definitions and theorems the same as their counterparts in the
    standard library, wherever they overlap. *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(* From LF Require Import Maps. *)

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

(** Minimum nat *)
Fixpoint minimum (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | x :: t =>
    match minimum t with
    | None => Some x
    | Some y => Some (min x y)
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

Lemma le_SS : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Lemma plus_leb_r : forall (x y z : nat),
  x <= y -> x + z <= y + z.
Proof.
  intros x y z.
  generalize dependent y.
  generalize dependent x.
  induction z as [|z' IH].
  - intros x y. intros H.
    rewrite plus_0_r. rewrite plus_0_r. apply H.
  - intros x y. intros H.
    rewrite <- plus_Snm_nSm.
    rewrite <- plus_Snm_nSm.
    apply IH.
    apply le_SS. apply H.
Qed.

Lemma plus_leb_l : forall (x y z : nat),
  x + z <= y + z -> x <= y.
Proof.
  intros x y z.
  generalize dependent y.
  generalize dependent x.
  induction z as [|z' IH].
  - intros x y. intros H.
    rewrite plus_0_r in H.
    rewrite plus_0_r in H.
    apply H.
  - intros x y. intros H.
    rewrite <- plus_Snm_nSm in H.
    rewrite <- plus_Snm_nSm in H.
    apply IH in H.
    inversion H.
    + reflexivity.
    + transitivity (S x).
      * apply le_S. reflexivity.
      * apply H1.
Qed.

Lemma combine_leb : forall x1 y1 x2 y2 : nat,
  x1 <= y1 ->
  x2 <= y2 ->
    x1 + x2 <= y1 + y2.
Proof.
  intros x1 y1 x2 y2.
  intros H1 H2.
  transitivity (x1 + y2).
  - rewrite plus_comm. rewrite (plus_comm x1).
    apply plus_leb_r. apply H2.
  - apply plus_leb_r. apply H1.
Qed.

Lemma lebP : forall n m, reflect (n <= m) (n <=? m).
Proof.
  intros n m. apply iff_reflect. split.
  - intros H. apply leb_correct. apply H.
  - intros H. apply leb_complete. apply H.
Qed.

Lemma O_leb_O : forall i,
  i <= 0 -> i = 0.
Proof.
  intros i.
  intros H.
  inversion H.
  reflexivity.
Qed.

Lemma leb_trans : forall i j k,
  i <= j -> j <= k ->
    i <= k.
Proof.
  intros i j k.
  intros H1 H2.
  transitivity j.
  - apply H1.
  - apply H2.
Qed.

Lemma app_suf_eq : forall {A : Type} (xs : list A) ys zs,
  xs = ys -> xs ++ zs = ys ++ zs.
Proof.
  intros A xs ys zs.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma app_pref_eq : forall {A : Type} (l l' pref : list A),
  pref ++ l = pref ++ l' -> l = l'.
Proof.
  intros A l l' pref.
  induction pref as [|h t].
  - simpl. intros H. apply H.
  - intros H. rewrite <- app_comm_cons in H. rewrite <- app_comm_cons in H.
    injection H as H. apply IHt in H. apply H.
Qed.

Lemma app_pref_eq' : forall {A : Type} (l l' pref : list A),
  l = l' -> pref ++ l = pref ++ l'.
Proof.
  intros A l l' pref.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma app_pref_eq_r' : forall {A : Type} (l l' pref : list A),
  l = l' -> l ++ pref = l' ++ pref.
Proof.
  intros A l l' pref.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma minus_plus : forall x y z,
  y <= x ->
    (x - y) + z = (x + z) - y.
Proof.
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
Qed.

Lemma plus_minus : forall x y z,
  (x + y) - (y + z) = x - z.
Proof.
  intros x y z.
  induction y as [|y' IH].
  - simpl. rewrite plus_0_r. reflexivity.
  - simpl. rewrite <- plus_Snm_nSm. simpl. apply IH.
Qed.

(** Tree Substitution Grammar parser, 1st try.
*)


(** Termina (position) in the input sentence *)
Definition term := nat.

Inductive symbol {nt t} : Type :=
  | NonTerm (x : nt)
  | Terminal (x : t).

(*
Inductive rule {v : Type} :=
  | Rule (head : v) (body : list v).

Definition head {v : Type} (r : @rule v) : v :=
  match r with
  | Rule x y => x
  end.

Definition body {v : Type} (r : @rule v) : list v :=
  match r with
  | Rule x y => y
  end.

(* Leading symbol in the body of the rule *)
Definition lead (r : rule) : option node :=
  match r with
  | Rule _ (h :: t) => Some h
  | _ => None
  end.

(* Shift the dot in the rule (if possible) *)
Definition shift (r : rule) : rule :=
  match r with
  | Rule x (h :: t) => Rule x t
  | _ => r
  end.
*)

(*
(* Shift the dot in the rule (if possible) *)
Definition shift {v : Type} (r : @rule v) : option (v * @rule v) :=
  match r with
  | Rule x (h :: t) => Some (h, Rule x t)
  | _ => None
  end.
*)

(* Weight; eventually should be represented by a real number? *)
Definition weight := nat.

(* fmap for an option *)
Definition fmap
  {A B : Type} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some v => Some (f v)
  end.

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
      (* node labeling function *)

  ; root_has_non_term : forall v,
      root v = true ->
        exists x, label v = NonTerm x
      (* label assigned to a root is a non-terminal *)

  ; parent : vert -> option vert
      (* parent of the given vertex (root => None) *)
  ; children : vert -> list vert
      (* the list of children of the given vertex (leaf => nil) *)

(*
  ; rule_for : vert -> @rule vert
      (* production rule for the given vertex 
         NOTE: returns a trivial rule for a leaf; we don't
         use such rules our inference system! (but we could...) *)
*)

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

  ; shift_inf' : forall r r' v,
      shift r = Some (v, r') ->
        inf v ++ inf' r = inf' r'
      (* this one is somewhat dangerous! *)

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
        inf' r' = inf' r
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

Lemma inf_tail_empty : forall {vt nt}
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

(** The list (=>set) of production rules in the grammar *)
Definition rules {vt nt} (g : @Grammar vt nt) : list (vt*nat) :=
  let
    f v :=
      if leaf g v
      then None
      else Some (v, 0)
  in
    map_maybe f (vertices g).

(*
(** The last position in the sentence *)
Definition term_max {vt nt} (g : @Grammar vt nt) : term :=
  match maximum (terminals g) with
  | None => 0 (* WARNING: this should never happen! *)
  | Some x => x
  end.
*)

(*
(** Weight of the ET with the given rule *)
Definition rule_weight {vt nt}
    (g : @Grammar vt nt) (r : vt * nat) : weight :=
  tree_weight g (fst r). *)

(** Weight of the given (dependent, head) arc +
    weight of the dependent ET
*)
Definition omega {vt nt}
    (g : @Grammar vt nt) (dep gov : vt) : weight :=
  arc_weight g (anchor g dep) (anchor g gov) +
  tree_weight g dep.

(*
(** Weight of the ET with the given rule, provided that it contains
    the given terminal anchor terminal. *)
Definition rule_with_term_weight {vt nt}
    (g : @Grammar vt nt) (t : term) (r : vt * nat) : option weight :=
  if anchor g (fst r) =? t
  then Some (rule_weight g r)
  else None. *)

(** The minimal cost of scanning the given terminal *)
Definition cost {vt nt} (g : @Grammar vt nt) (t : term) : weight :=
  min_arc_weight g t + min_tree_weight g t.

(*
(** The minimal cost of scanning the given terminal *)
Definition cost {vt nt}
    (g : @Grammar vt nt) (t : term) : weight :=
  match minimum (cat_maybes (map (rule_with_term_weight g t) (rules g))) with
  | None => 0
  | Some x => x
  end.
*)

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

(*
Definition shift {vt nt}
    (g : @Grammar vt nt) (r : vt*nat) : option (vt * (vt*nat)) :=
  match r with
  | (v, k) =>
      match drop k (children g v) with
      | v' :: t => Some (v', (v, k+1))
      | [] => None
      end
  end.
*)

Definition lead {vt nt}
    (g : @Grammar vt nt) (r : vt*nat) : option vt :=
  match shift g r with
  | Some (v, _) => Some v
  | None => None
  end.

(*
Axiom shift_inf : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r = Some (v, r') ->
    inf' g r ++ inf g v = inf' g r'.

Lemma shift_inf_passive : forall {vt nt} (g : @Grammar vt nt) r,
  shift g r = None -> 
    inf' g r = inf g (fst r).
Proof.
Admitted.

Lemma shift_term_inf : forall {vt nt} (g : @Grammar vt nt) r r' v i,
  shift g r = Some (v, r') ->
  label g v = Terminal i ->
    inf' g r' = inf' g r ++ [i].
Proof.
  intros vt nt g r r' v i.
  intros H1 H2.
  apply shift_inf in H1 as H3.
  (* At this point we need to know that [inf leaf]
     is simply defined in terms of the symbol in the [leaf].
  *)
Admitted.

Lemma shift_non_term_leaf_inf : forall {vt nt} (g : @Grammar vt nt) r r' v x,
  shift g r = Some (v, r') ->
  leaf g v = true ->
  label g v = NonTerm x ->
    inf' g r' = inf' g r.
Proof.
Admitted.


Lemma no_shift_inf : forall {vt nt} (g : @Grammar vt nt) r,
  shift g r = None ->
    inf' g r = inf g (fst r).
Proof.
Admitted.
*)

(*
Lemma shift_preserves_head : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r = Some (v, r') -> fst r = fst r'.
Proof.
  intros vt nt g [v k] [v' k'] v'' H.
  simpl.
  unfold shift in H.
  destruct (drop k (children g v)) eqn:E.
  - discriminate H.
  - injection H. intros _ H' _. apply H'.
Qed.
*)

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

(*
Lemma shift_sup' : forall {vt nt}
    (g : @Grammar vt nt) (r r' l : vt*nat),
  shift g r = Some (fst l, r') ->
  shift g l = None ->
    sup' g r' = inf' g l ++ sup' g r.
Proof.
Admitted.
*)

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
  (* assert (H': inf' g r = []). *)
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

(*
Lemma app_suf_eq : forall {A : Type} (xs : list A) ys zs,
  xs = ys -> xs ++ zs = ys ++ zs.

Lemma app_pref_eq : forall {A : Type} (l l' pref : list A),
  pref ++ l = pref ++ l' -> l = l'.

  ; inf_plus_sup' :
      forall (r : vert * nat),
        inf' r ++ sup' r = [anchor (fst r)]
*)

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
  rewrite (minus_plus
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
  rewrite (minus_plus _ (costs g (sup g v))).
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
    assert (H3: j = 0). { apply O_leb_O in H2. apply H2. }
    assert (H4: i = 0). { rewrite H3 in H1. apply O_leb_O in H1. apply H1. }
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
Definition rest {vt nt} (g : @Grammar vt nt) (i j : term) : list term :=
  in_span 0 (i - 1) ++ in_span (j + 1) (term_max g).

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
      (* (E: fmap (label g) (lead g r) = Some (terminal j)) : *)
      (E1: shift g r = Some (v, r'))
      (E2: label g v = Terminal j) :
        item g r' i (S j) w (*(heuristic g r' i (S j))*)
          (total g r i j w)
  | pseudo_subst
      (g : @Grammar vt nt) (l r l' : vt*nat) (i j k : term) (w1 w2 _t1 _t2 : weight)
      (LP: item g l i j w1 _t1)
      (RP: item g r j k w2 _t2)
      (L: shift g r = None)
      (E: shift g l = Some (fst r, l')) :
        item g l' i k (w1 + w2) (*(heuristic g l' i k)*)
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
        item g l' i k (w1 + w2 + omega g (fst r) (fst l)) (*(heuristic g l' i k)*)
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
      rewrite (shift_non_term_leaf_inf g l l' v x).
      * apply IHL.
      * apply L3.
      * apply L4.
      * rewrite L2' in E. apply E.
Qed.

(* TODO: not correct! use in_vs_inside
Lemma inf_complete_eq_in_span : forall {vt nt} 
  (g : @Grammar vt nt) r i j w t
  (I: @item vt nt g r i j w t),
    shift g r = None ->
      inf g (fst r) = in_span i j.
Proof.
Admitted.
*)

Lemma rest_Sj : forall {vt nt} (g : @Grammar vt nt) (i j : term),
  i <= j -> rest g i j = rest g i (S j) ++ [j].
Proof. Admitted.
(*
  intros i j H.
  simpl.
  destruct (lebP i j) as [H'|H'].
  - reflexivity.
  - apply H' in H. destruct H.
Qed. *)

Lemma cost_rest_min_in : forall {vt nt}
  (g : @Grammar vt nt) (i j k : term),
    costs g (rest g i k) = costs g (rest g i j) - costs g (in_span j k).
Proof.
Admitted.

Lemma cost_rest_plus_in_l : forall {vt nt}
  (g : @Grammar vt nt) (i j k : term),
    costs g (rest g j k) = costs g (in_span i j) + costs g (rest g i k).
Proof.
Admitted.

Lemma cost_rest_plus_in_r : forall {vt nt}
  (g : @Grammar vt nt) (i j k : term),
    costs g (rest g i j) = costs g (rest g i k) + costs g (in_span j k).
Proof.
Admitted.

Lemma amort_weight_complete : forall {vt nt}
  (g : @Grammar vt nt) (r : vt*nat),
    shift g r = None ->
      amort_weight g (fst r) = amort_weight' g r.
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
  - simpl. apply Peano.le_0_n.
  - unfold total.
    rewrite (plus_comm w'). rewrite (plus_comm w').
    apply plus_leb_r.
    unfold heuristic.
    apply shift_amort_weight in E1 as E1'.
    rewrite E1'.
    rewrite <- plus_assoc.
    apply combine_leb. reflexivity.
    apply (item_i_leb_j r1 i' j' w') in P as P'.
    apply (rest_Sj g) in P'.
    rewrite P'.
    rewrite costs_app.
    apply term_inf in E2. rewrite E2.
    rewrite plus_comm.
    apply combine_leb.
    reflexivity.
    reflexivity.
  - apply Nat.max_lub_iff. split.
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
      rewrite (plus_comm _ (costs g (rest g i' k))).
      rewrite <- plus_assoc.
      apply combine_leb. { reflexivity. }
      rewrite <- shift_inf_passive.
      Focus 2. apply L.
      rewrite plus_comm.
      apply (in_vs_inside r' j' k w2 _t2).
      apply RP.
    + unfold total.
      rewrite (plus_comm w1).
      rewrite <- plus_assoc.
      apply combine_leb. { reflexivity. }
      unfold heuristic.
      rewrite (cost_rest_plus_in_l g i' j' k).
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

(*
        unfold amort_weight'.
        apply shift_preserves_tree_weight in E as E1.
        apply shift_preserves_anchor in E as E2.
        rewrite E1. rewrite E2.
        rewrite (minus_plus
          (tree_weight g (fst l') + min_arc_weight g (anchor g (fst l')))
          (costs g (sup' g r'))).
        { apply (shift_sup' g) in E as E3.
          Focus 2. apply L.
          rewrite E3.
          rewrite costs_app.
          rewrite 

      unfold amort_weight'.

      apply shift_amort_weight in E as E'.
      rewrite E'.
*)
Qed.





