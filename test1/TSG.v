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

(** Tree Substitution Grammar parser, 1st try.
*)


(** Termina (position) in the input sentence *)
Definition term := nat.

Inductive symbol {nt t} : Type :=
  | non_term (x : nt)
  | terminal (x : t).

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

  ; root : vert -> bool
      (* is the given node a root of an ET? *)
  ; leaf : vert -> bool
      (* is the given node a leaf of an ET? *)
  ; anchor : vert -> term
      (* anchor terminal of the ET containing the given node *)
  ; label : vert -> @symbol non_term term
      (* node labeling function *)

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

  }.

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


(** Weight of the ET with the given rule *)
Definition rule_weight {vt nt}
    (g : @Grammar vt nt) (r : vt * nat) : weight :=
  tree_weight g (fst r).

(** Weight of the given (dependent, head) arc +
    weight of the dependent ET
*)
Definition omega {vt nt}
    (g : @Grammar vt nt) (dep gov : vt) : weight :=
  arc_weight g (anchor g dep) (anchor g gov) +
  tree_weight g dep.

(** Minimal arc weight for the given dependent *)
Definition min_arc_weight {vt nt}
    (g : @Grammar vt nt) (dep : term) : weight :=
  match minimum (map (arc_weight g dep) (terminals g)) with
  | None => 0
  | Some x => x
  end.

(** Weight of the ET with the given rule, provided that it contains
    the given terminal anchor terminal. *)
Definition rule_with_term_weight {vt nt}
    (g : @Grammar vt nt) (t : term) (r : vt * nat) : option weight :=
  if anchor g (fst r) =? t
  then Some (rule_weight g r)
  else None.

(** The minimal cost of scanning the given terminal *)
Definition cost {vt nt}
    (g : @Grammar vt nt) (t : term) : weight :=
  match minimum (cat_maybes (map (rule_with_term_weight g t) (rules g))) with
  | None => 0
  | Some x => x
  end.

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

Definition shift {vt nt}
    (g : @Grammar vt nt) (r : vt*nat) : option (vt * (vt*nat)) :=
  match r with
  | (v, k) =>
      match drop k (children g v) with
      | v' :: t => Some (v', (v, k+1))
      | [] => None
      end
  end.

Definition lead {vt nt}
    (g : @Grammar vt nt) (r : vt*nat) : option vt :=
  match shift g r with
  | Some (v, _) => Some v
  | None => None
  end.

Axiom shift_inf : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r = Some (v, r') ->
    inf' g r ++ inf g v = inf' g r'.

Lemma app_pref_eq : forall {A : Type} (l l' pref : list A),
  pref ++ l = pref ++ l' -> l = l'.
Proof.
  intros A l l' pref.
  induction pref as [|h t].
  - simpl. intros H. apply H.
  - intros H. rewrite <- app_comm_cons in H. rewrite <- app_comm_cons in H.
    injection H as H. apply IHt in H. apply H.
Qed.

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

(** Amortized weight of the given parsing configuration *)
Definition amort_weight {vt nt} (g : @Grammar vt nt) (n : vt) : weight :=
  tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup g n).

(** Amortized weight of the given parsing configuration *)
Definition amort_weight' {vt nt} (g : @Grammar vt nt) (r : vt*nat) : weight :=
  let n := fst r
  in tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup' g r).

Lemma minus_plus : forall x y z, (x - y) + z = x + (z - y).
Proof.
Admitted.

Lemma plus_minus : forall x y z, z + (x - (x + y)) = z - y.
Proof.
Admitted.

Lemma shift_amort_weight : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r' = Some (v, r) ->
    amort_weight' g r = amort_weight' g r' + costs g (inf g v).
Proof.
  intros vt nt g r r' v H.
  unfold amort_weight'.
  apply shift_preserves_head in H as H'.
  rewrite H'.
  (* Unset Printing Notations. *)
  rewrite minus_plus.
  rewrite (shift_cost_sup g r r') with (v := v).
  - rewrite plus_minus. reflexivity.
  - apply H.
Qed.

(** Chart items and the rules to infer them. *)
Inductive item {vt nt} : vt*nat -> term -> term -> weight -> Prop :=
  | axiom (g : @Grammar vt nt) (r : vt*nat) (i : term)
      (I: In r (rules g))
      (L: i <= term_max g) :
        item r i i 0
  | scan (g : @Grammar vt nt) (r : vt*nat) (i : term) (j : term) (w : weight)
      (P: item r i j w)
      (L: j <= term_max g)
      (E: fmap (label g) (lead g r) = Some (terminal j)) :
        item r i (S j) w
  | pseudo_subst
      (g : @Grammar vt nt) (l r l' : vt*nat) (i j k : term) (w1 w2 : weight)
      (LP: item l i j w1)
      (RP: item r j k w2)
      (L: shift g r = None)
      (E: shift g l = Some (fst r, l')) :
        item l' i k (w1 + w2)
  | subst
      (g : @Grammar vt nt) (l r l' : vt*nat) (i j k : term) (v : vt) (w1 w2 : weight)
      (LP: item l i j w1)
      (RP: item r j k w2)
      (L1: shift g r = None)
      (L2: root g (fst r) = true)
      (L3: shift g l = Some (v, l'))
      (L4: leaf g v = true)
      (E: label g v = label g (fst r)) :
        item l' i k (w1 + w2 + omega g (fst r) (fst l)).



