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

(** Grammar representation *)
Record Grammar := mkGram
  { rule_set : list rule (* TODO: use a real set data type? *)
      (* The set of grammar production rules *)
  ; label : node -> symbol
      (* node labeling function *)
  ; term_max: nat
      (* the last terminal (position) in the sentence *)
  ; root : node -> bool
      (* is the given node a root of an ET? *)
  ; leaf : node -> bool
      (* is the given node a leaf of an ET? *)
  }.

(*
 ; Rat_bottom_cond : 0 <> bottom
 ; Rat_irred_cond :
     forall x y z:nat, (x * y) = top /\ (x * z) = bottom -> x = 1
 }.
*)

(* Chart items and the rules to infer them. *)
Inductive item : dotted_rule -> pos -> pos -> Prop :=
  | axiom (g : Grammar) (r : rule) (i : pos)
      (I: In r (rule_set g))
      (L: i <= term_max g) :
        item r i i
  | scan (g : Grammar) (r : rule) (i : pos) (j : pos)
      (P: item r i j)
      (L: j <= term_max g)
      (E: fmap (label g) (lead r) = Some (term j)) :
        item r i (S j)
  | pseudo_subst (g : Grammar) (l : rule) (r : rule) (i j k : pos)
      (LP: item l i j)
      (RP: item r j k)
      (L: body r = [])
      (E: lead l = Some (head r)) :
        item (shift l) i k
  | subst (g : Grammar) (l : rule) (r : rule) (i j k : pos)
      (LP: item l i j)
      (RP: item r j k)
      (L1: body r = [])
      (L2: root g (head r) = true)
      (L3: fmap (leaf g) (lead l) = Some true)
      (E: fmap (label g) (lead l) = Some (label g (head r))) :
        item (shift l) i k.