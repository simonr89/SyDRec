Require Import List.
Import ListNotations.
Require SyDRec.Morphisms. (* provides the Catamorphism command *)

Inductive tree (T : Type) : Type :=
| leaf : T -> tree T
| node : T -> tree T -> tree T -> tree T.

Arguments leaf {T} _.
Arguments node {T} _ _ _.

(* This command declares the catamorphism function of type tree as
   well as the associated fusion theorem *)
Catamorphism tree.

Print cata_tree.

Print cata_tree_fusion.

(* Some examples of applied catamorphisms *)
Definition count {T} : tree T -> nat :=
  cata_tree (fun _ => 1) (fun _ l r => 1 + l + r).

Definition depth {T} : tree T -> nat :=
  cata_tree (fun _ => 1) (fun _ l r => 1 + max l r).

Definition flatten {T} : tree T -> list T :=
  cata_tree (fun x => [x]) (fun x l r => l ++ x :: r).

Definition sym {T} : tree T -> tree T :=
  cata_tree leaf (fun x l r => node x r l).

Definition map {A B} (f : A -> B) : tree A -> tree B :=
  cata_tree (fun x => leaf (f x)) (fun x l r => node (f x) l r).

(* Here is an application of the fusion theorem *)
Require Import Program.Basics.
Open Scope program_scope. (* composition Notation *)

Lemma map_map_promotion {A B C} (f : A -> B) (g : B -> C) :
  forall t, map g (map f t) = map (g ∘ f) t.
Proof.
  intros t. apply cata_tree_fusion.
  - auto.
  - auto.
Qed.

(* Catamorphism generation also works for types with real
   arguments. Here is an example with height-indexed trees.*)
Inductive ntree (T : Type) : nat -> Type :=
  | nleaf : T -> ntree T 1
  | nnode : forall n m, T -> ntree T n -> ntree T m -> ntree T (S (max n m)).

Catamorphism ntree.

Print cata_ntree.

Print cata_ntree_fusion.

Definition to_tree {T n} : ntree T n -> tree T :=
  cata_ntree leaf (fun _ _ x l r => node x l r).

Lemma flatten_to_tree_promotion {T n} :
  forall (t : ntree T n),
    flatten (to_tree t) = cata_ntree (fun x => [x]) (fun _ _ x l r => l ++ x :: r) t.
Proof.
  intros t. apply cata_ntree_fusion.
  - auto.
  - auto.
Qed.

(* However catamorphisms ranging over dependent types cannot be
   defined. More precisely, the higher-oder function that is needed to
   accomplish this is already provided: it is the general induction
   principle foo_rect. However no (useful) fusion theorem can be
   generated for this function *)

(* Paramorphisms are slightly more general than catamorphisms. They
   allow the definition of functions that recursively apply to
   recursive constructor arguments but also use these arguments. An
   archetypal example is the factorial function. *)
Paramorphism nat.

Definition factorial : nat -> nat :=
  para_nat 1 (fun n m => m * S n).

(* For comparison, it is possible, yet awkward, to define the
   factorial function using catamorphisms.*)
Catamorphism nat.

Definition factorial_aux : nat -> nat * nat :=
  cata_nat (0, 1) (fun p => let (n, m) := p in (S n, m * S n)).

(* Since we can't directly use the value of the recursive constructor
   argument for computation with catamorphisms, we artificially keep
   track of it in a pair.*)
Lemma factorial_aux_lemma :
  forall n, factorial_aux n = (n, factorial n).
Proof.
  intros n. induction n.
  - auto.
  - simpl. rewrite IHn. auto.
Qed.
  
Definition factorial' : nat -> nat :=
  compose (@snd nat nat) factorial_aux.