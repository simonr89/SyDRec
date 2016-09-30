(* This file provides an example of constructive program derivation,
   where the aim is to construct a more efficient expression of a
   function, and not merely to prove an equality.*)

Require SyDRec.Catamorphism.
Require Import SyDRec.Constructive.

Inductive tree (T : Type) : Type :=
| leaf : T -> tree T
| node : T -> tree T -> tree T -> tree T.

Arguments leaf {T} _.
Arguments node {T} _ _ _.

Catamorphism tree.

Definition count {T} : tree T -> nat :=
  cata_tree (fun _ => 1) (fun _ l r => 1 + l + r).

Definition map {A B} (f : A -> B) : tree A -> tree B :=
  cata_tree (fun x => leaf (f x)) (fun x l r => node (f x) l r).

(* We must use Definition instead of Theorem or Lemma, otherwise the
   definition will be opaque and we won't be able to reuse the
   instances of c1 and c2 that we provided.*)
Definition map_map_promotion' {A B C} (f : A -> B) (g : B -> C) :
  {c1, c2 | forall t, map g (map f t) = cata_tree c1 c2 t}.
Proof.
  econstructor.
  intro.
  apply cata_tree_fusion.
  - intros; simpl. beta. reflexivity.
  - intros; simpl. do 3 beta. reflexivity.
Defined.

(* Here's how to reuse the catamorphism instance we've just
   constructed *)
Lemma map_map_length_promotion {A B C} (f : A -> B) (g : B -> C) :
  forall t, count (map g (map f t)) = count t.
Proof.
  intro t.
  (* this tactic applies a projection on the term so that we get the
  lemma we need *)
  assert_proj2 (map_map_promotion' f g).
  rewrite H.
  apply cata_tree_fusion.
  - auto.
  - auto.
Qed.