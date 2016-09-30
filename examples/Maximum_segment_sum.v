(** This file showcases the use of catamorphisms and fusion theorems
    for program optimization with a concrete example. A specification
    for the maximum segment sum problem is given as a composition of
    catamorphisms on lists, and the fusion theorem is used to derive
    an efficient expression of this function. This work is a
    formalization of the following article:

    Gibbons, J. (2002). Calculating functional programs. In Algebraic
    and Coalgebraic Methods in the Mathematics of Program Construction
    (pp. 151-203). Springer Berlin Heidelberg.*)

Require Import List.
Import ListNotations.
Require Import ZArith.BinInt.
Require Import Program.Basics.
Require SyDRec.Catamorphism.

Class Monoid {A : Type} (f : A -> A -> A) (e : A) : Prop :=
  { assoc : forall x y z, f x (f y z) = f (f x y) z;
    unit_l : forall x, f e x = x ;
    unit_r : forall x, f x e = x
  }.

(** * Datatype and operations *)

(** The datatype we use is that of integers extended with a infimum,
    thus making it a semilattice. The plus and max operations are
    extended accordingly.*)

Inductive Z_ext : Type :=
| Inf : Z_ext
| OfZ : Z -> Z_ext.

Definition zero : Z_ext := OfZ Z0.

Definition plus (a b : Z_ext) : Z_ext :=
  match a, b with
    | Inf, _ => Inf
    | _, Inf => Inf
    | OfZ a, OfZ b => OfZ (Zplus a b)
  end.

Definition max (a b : Z_ext) : Z_ext :=
  match a, b with
    | Inf, _ => b
    | _, Inf => a
    | OfZ a, OfZ b => OfZ (Zmax a b)
  end.

Lemma max_assoc:
  forall x y z, max x (max y z) = max (max x y) z.
Proof.
  intros x y z. destruct x, y, z; try auto.
  simpl; rewrite Z.max_assoc; trivial.
Qed.

Lemma max_unit_r:
  forall x, max x Inf = x.
Proof.
  intros x. destruct x; auto.
Qed.

Lemma max_unit_l:
  forall x, max Inf x = x.
Proof.
  intros x. destruct x; auto.
Qed.

Instance ZextMonoid : Monoid max Inf.
Proof.
  split.
  apply max_assoc.
  apply max_unit_l.
  apply max_unit_r.
Qed.

(** * Catamorphisms *)

(** In this section we automatically generate the catamorphism
    associated with the datatype of lists, as well as its fusion
    theorem. We also define the operations that we will use as
    catamorphisms (some of which are already defined as ad hoc
    functions in the standard library.*)

Catamorphism list.

(** ** Definitions *)

Definition append {A} (l1 l2: list A) : list A :=
  cata_list l2 (@cons A) l1.

Definition map {A B} (f : A -> B) : list A -> list B :=
  cata_list [] (fun x xs => f x :: xs).

Definition concat {A} : list (list A) -> list A :=
  cata_list [] append.

Definition sum : list Z_ext -> Z_ext :=
  cata_list zero plus.

(* The default values for the head function do not matter since they
   are not used in these cases. Other versions of head (either taking
   a sig list as an input, or outputting an option A) are more
   difficult to use in this setting.*)
Definition tails {A} : list A -> list (list A) :=
  cata_list [[]] (fun a xss => (a :: hd [] xss) :: xss).

Definition scan {A B} (e : B) (f : A -> B -> B) : list A -> list B :=
  cata_list [e] (fun a bs => f a (hd e bs) :: bs).

Definition inits {A} : list A -> list (list A) :=
  cata_list [[]] (fun a xss => [] :: map (cons a) xss).

Definition maximum: list Z_ext -> Z_ext :=
  cata_list Inf max.

(** The function segs returns the list of all sublists of a list.*)
Definition segs {A} (l : list A) : list (list A) :=
  concat (map inits (tails l)).

(** This is the specification of the maximum segment sum problem: this
    function computes the maximum of the sums of all the sublists of a
    given list. This naive expression has order of n³ time complexity
    (the time required to map inits to all the tails when generating
    the list of segments). Our goal is to apply multiple
    transformation steps, all based on the fusion theorem, in order to
    obtain an equivalent, more efficient expression of the function.*)
Definition mss (l : list Z_ext) : Z_ext :=
  maximum (map sum (segs l)).

(** ** Promotion lemmas *)

Open Scope program_scope. (* Used for the composition notation *)

Lemma map_map_promotion {A B C} :
  forall (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (g ∘ f) l.
Proof.
  intros f g l.
  apply cata_list_fusion; intros; auto.
Qed.

Lemma map_append {A B} :
  forall (f : A -> B) (l1 l2 : list A),
    map f (append l1 l2) = append (map f l1) (map f l2).
Proof.
  intros f l1 l2. generalize l2. induction l1; intro l0.
  - auto.
  - simpl. rewrite IHl1. trivial.
Qed.

Lemma cata_map_promotion {A B C} :
  forall (e : C) (f : B -> C -> C) (g : A -> B) (l : list A),
    cata_list e f (map g l) = cata_list e (fun x xs => f (g x) xs) l.
Proof.
  intros f e g l.
  apply cata_list_fusion; intros; auto.
Qed.

(** By itself, this transformation does not improve efficiency: in
    fact the right-hand side uses more intermediate data
    structures. However we use this rule as an intermediate rewriting
    step.*)
Lemma map_concat_promotion {A B} :
  forall (f : A -> B) (ll : list (list A)),
    map f (concat ll) = concat (map (map f) ll).
Proof.
  intros f ll. unfold concat. rewrite cata_map_promotion.
  apply cata_list_fusion.
  - auto.
  - intros. simpl. rewrite map_append. auto.
Qed.

Lemma cata_append {A} :
  forall (f : A -> A -> A) (e : A) (l1 l2 : list A),
    Monoid f e ->
    cata_list e f (append l1 l2) =
    f (cata_list e f l1) (cata_list e f l2).
Proof.
  intros f e l1 l2 H; destruct H.
  induction l1.
  - simpl. rewrite unit_l0. trivial.
  - simpl. rewrite IHl1. rewrite assoc0. trivial.
Qed.

(** This rule too is meant only to be used as an intermediate step
    rather an optimizing transformation.*)
Lemma cata_concat_promotion {A} :
  forall (f : A -> A -> A) (e : A) (ll : list (list A)),
    Monoid f e ->
    cata_list e f (concat ll) =
    cata_list e f (map (cata_list e f) ll).
Proof.
  intros f e ll H. rewrite cata_map_promotion.
  apply cata_list_fusion.
  - auto.
  - intros; simpl.
    symmetry; rewrite cata_append; auto.
Qed.

Lemma scan_lemma_helper {A B} :
  forall (f : A -> B) l d,
    f (hd d l) = hd (f d) (map f l).
Proof.
  intros f l d1. destruct l; auto.
Qed.

(** This equality can alternatively be seen as a specification of
    scan.*)
Lemma scan_lemma {A B} :
  forall (f : A -> B -> B) (e : B) (l : list A),
    map (cata_list e f) (tails l) = scan e f l.
Proof.
  intros f e l. apply cata_list_fusion.
  - auto.
  - intros; simpl.
    symmetry; rewrite scan_lemma_helper.
    auto.
Qed.

Lemma sum_inits_helper:
  forall (x : Z_ext) (ll : list (list Z_ext)),
    map sum (map (cons x) ll) =
    map (fun y => plus x y) (map sum ll).
Proof.
  intros n ll. induction ll.
  - auto.
  - simpl; rewrite IHll. auto.
Qed.

Lemma sum_inits_promotion:
  forall (l : list Z_ext),
    map sum (inits l) = cata_list [zero] (fun x xs => zero :: map (fun y => plus x y) xs) l.
Proof.
  apply cata_list_fusion.
  - auto.
  - intros. simpl. rewrite sum_inits_helper. auto.
Qed.

Lemma maximum_plus_distrib:
  forall x l,
    maximum (map (plus x) l) = plus x (maximum l).
Proof.
  intros x l. induction l; destruct x; try auto.
  - simpl. rewrite IHl. destruct a.
    * auto.
    * destruct (maximum l).
      + auto.
      + simpl. rewrite Z.add_max_distr_l. auto.
Qed.

(** This transformation turns a O(n²) function into a O(n).*)
Lemma maximum_mapsum_inits_promotion:
  forall (l : list Z_ext),
    maximum (map sum (inits l)) =
    cata_list zero (fun a b => max zero (plus a b)) l.
Proof.
  intro l.
  rewrite sum_inits_promotion. apply cata_list_fusion.
  - auto.
  - intros; simpl. rewrite maximum_plus_distrib; auto.
Qed.

(** This lemma is helpful to rewrite map expressions.*)
Lemma map_extensionality {A B} {f g : A -> B} :
    (forall x, f x = g x) -> forall l, map f l = map g l.
Proof.
  intros H l; induction l.
  - auto.
  - simpl. rewrite IHl, H. auto.
Qed.

(** In this final calculation, we derive an equivalent expression of
    the maximum segment sum function. The resulting expression takes
    linear time and require only one intermediate list.*)
Definition f (a b : Z_ext) : Z_ext :=
  max zero (plus a b).

Theorem mss_opt:
  forall (l : list Z_ext),
    mss l = maximum (scan zero f l).
Proof.
  intro l. unfold mss, segs.
  rewrite map_concat_promotion. unfold maximum.
  rewrite (cata_concat_promotion _ _ _ ZextMonoid).
  do 2 rewrite map_map_promotion.
  fold maximum.
  rewrite (map_extensionality maximum_mapsum_inits_promotion).
  rewrite scan_lemma.
  reflexivity.
Qed.