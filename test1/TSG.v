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

From LF Require Import Maps.


(** Tree Substitution Grammar parser, 1st try.
*)


Definition non_terminal := string.
Definition terminal := nat.


Inductive symbol : Type :=
  | non_term (x : non_terminal)
  | term (x : terminal).


(** Node.  Eventually, should be constrained to a closed, predefined set.
*)
Definition node := nat.

Inductive rule : Type :=
  | Rule (head : node) (body : list node).


Definition head (r : rule) : node :=
  match r with
  | Rule x y => x
  end.


Definition body (r : rule) : list node :=
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


(* Shift the dot in the rule (if possible) *)
Definition shift' (r : rule) : option (node * rule) :=
  match r with
  | Rule x (h :: t) => Some (h, Rule x t)
  | _ => None
  end.


(** We just assume that the dot is in front of the body.
    In a dotted rule, the body may not contain all the
    symbols in the actualy body of the rule, just the
    symbols that are still to be matched. 
*)
Definition dotted_rule := rule.

(** Position in the input sentence.
*)
Definition pos := nat.

(* Weight; eventually should be represented by a real number? *)
Definition weight := nat.

(* Weight map assinging weights to slots in the input sentence. *)
Definition wmap := partial_map (weight*weight).

(*
Definition apply
  {A B : Type} (f : A -> option B) (x : option A) : option B :=
  match x with
  | None => None
  | Some v => 
    match f v with
    | None => None
    | Some v' => Some v'
    end
  end.
*)

(* fmap for an option *)
Definition fmap
  {A B : Type} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some v => Some (f v)
  end.


(** Ultimately, should have a full-fledged set representation.
*)
Definition set := list.


(** Grammar representation

TODO: there are many implicit assumptions not encoded in the record
type below.  For example, that the node arguments of the inidivudal 
functions actually belong to the grammar.

*)
Record Grammar := mkGram
  { rule_set : set rule
      (* the set of grammar production rules *)
  ; label : node -> symbol
      (* node labeling function *)
  ; term_max: nat
      (* the last terminal (position) in the sentence *)
  ; root : node -> bool
      (* is the given node a root of an ET? *)
  ; leaf : node -> bool
      (* is the given node a leaf of an ET? *)
  ; tree_weight : node -> weight
      (* weight of the ET containing the given node *)
  ; anchor : node -> terminal
      (* anchor terminal of the ET containing the given node *)
  ; arc_weight : terminal -> terminal -> weight
      (* weight of the given (dependency, head) arc *)

  ; inf : node -> set terminal
      (* the set of terminals under and in the given node. *)
  ; sup : node -> set terminal
      (* the set of terminals over the given node. *)
  ; inf_plus_sup :
      forall n : node,
        inf n ++ sup n = [anchor n]
      (* we assume that there is a single anchor in each ET;
         hence, the set of inferior plus the set of superior
         nodes should contain this unique anchor. *)

  ; inf' : dotted_rule -> set terminal
  ; sup' : dotted_rule -> set terminal
  ; inf_plus_sup' :
      forall r : dotted_rule,
        inf' r ++ sup' r = [anchor (head r)]
  }.


(** Weight of the ET with the given rule *)
Definition rule_weight (g : Grammar) (r : rule) : weight :=
  tree_weight g (head r).


(** Weight of the given (dependent, head) arc +
    weight of the dependent ET
*)
Definition omega (g : Grammar) (dep gov : node) : weight :=
  arc_weight g (anchor g dep) (anchor g gov) +
  tree_weight g dep.


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


(** Weight of the ET with the given rule, provided that it contains
    the given terminal anchor terminal. *)
Definition rule_with_term_weight
    (g : Grammar) (t : terminal) (r : rule) : option weight :=
  if anchor g (head r) =? t
  then Some (rule_weight g r)
  else None.


Fixpoint cat_maybes {A : Type} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some h :: t => h :: cat_maybes t
  | None :: t => cat_maybes t
  end.


Check map.


(** The minimal cost of scanning the given terminal *)
Definition cost (g : Grammar) (t : terminal) : weight :=
  match minimum (cat_maybes (map (rule_with_term_weight g t) (rule_set g))) with
  | None => 0
  | Some x => x
  end.


(** The minimal cost of scanning the given set of terminals *)
Definition costs (g : Grammar) (ts : set terminal) : weight :=
  fold_left plus (map (cost g) ts) 0.


Lemma sup_shift : forall (g : Grammar) (r : rule),
  match shift' r with
  | None => True
  | Some (h, r') =>
      costs g (sup' g r) = costs g (sup' g r') - costs g (inf g h)
  end.
Proof.
  intros g r.
  destruct r as [hd bd].
  induction bd.
  - (* [] *)
    simpl. apply I.
  - (* a :: bd *)
    simpl. simpl in IHbd.
    destruct bd as [|bd1 bds] eqn:E.
    + unfold sup'.
Admitted.


(** Chart items and the rules to infer them. *)
Inductive item : dotted_rule -> pos -> pos -> weight -> Prop :=
  | axiom (g : Grammar) (r : rule) (i : pos)
      (I: In r (rule_set g))
      (L: i <= term_max g) :
        item r i i 0
  | scan (g : Grammar) (r : rule) (i : pos) (j : pos) (w : weight)
      (P: item r i j w)
      (L: j <= term_max g)
      (E: fmap (label g) (lead r) = Some (term j)) :
        item r i (S j) w
  | pseudo_subst (g : Grammar) (l r : rule) (i j k : pos) (w1 w2 : weight)
      (LP: item l i j w1)
      (RP: item r j k w2)
      (L: body r = [])
      (E: lead l = Some (head r)) :
        item (shift l) i k (w1 + w2)
  | subst (g : Grammar) (l : rule) (r : rule) (i j k : pos) (w1 w2 : weight)
      (LP: item l i j w1)
      (RP: item r j k w2)
      (L1: body r = [])
      (L2: root g (head r) = true)
      (L3: fmap (leaf g) (lead l) = Some true)
      (E: fmap (label g) (lead l) = Some (label g (head r))) :
        item (shift l) i k (w1 + w2 + omega g (head r) (head l)).