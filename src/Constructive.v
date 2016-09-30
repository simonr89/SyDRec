(* Copyright Université d'Orléans (France)
   contributor : Simon Robillard (2014)
   simon.robillard@univ-orleans.fr

   This software is a computer program whose purpose is to provide
   functionalities to construct and derive programs with the Coq Proof
   Assistant.

   This software is governed by the CeCILL-C license under French law
   and abiding by the rules of distribution of free software.  You can
   use, modify and/ or redistribute the software under the terms of
   the CeCILL-C license as circulated by CEA, CNRS and INRIA at the
   following URL "http://www.cecill.info".

   As a counterpart to the access to the source code and rights to
   copy, modify and redistribute granted by the license, users are
   provided only with a limited warranty and the software's author,
   the holder of the economic rights, and the successive licensors
   have only limited liability.

   In this respect, the user's attention is drawn to the risks
   associated with loading, using, modifying and/or developing or
   reproducing the software by the user in light of its specific
   status of free software, that may mean that it is complicated to
   manipulate, and that also therefore means that it is reserved for
   developers and experienced professionals having in-depth computer
   knowledge. Users are therefore encouraged to load and test the
   software's suitability as regards their requirements in conditions
   enabling the security of their systems and/or data to be ensured
   and, more generally, to use and operate it in the same conditions
   as regards security.

   The fact that you are presently reading this means that you have
   had knowledge of the CeCILL-C license and that you accept its
   terms. *)

(* This module provides the beta tactic as well as the following
   definitions to allow constructive program derivations in Coq.*)
Declare ML Module "beta_plugin".

(* Since we cannot combine sig types likes we can with ex
   propositions, he are definitions of sig for n-ary
   propositions. This results in a lot of similar definitions (one for
   each n, we provide here the definitions for n from 1 to 5) but
   tactics allow for smooth proofs (which wouldn't be the case if we
   used tuples). Suggestions for a more elegant solution are
   welcome.*)
Inductive sig2var {A B : Type} (P : A -> B -> Prop) : Type :=
  exist_2var : forall x y, P x y -> sig2var P.

Inductive sig3var {A B C : Type} (P : A -> B -> C -> Prop) : Type :=
  exist_3var : forall x y z, P x y z -> sig3var P.

Inductive sig4var {A B C D : Type} (P : A -> B -> C -> D -> Prop) : Type :=
  exist_4var : forall x y z t, P x y z t -> sig4var P.

Inductive sig5var {A B C D E: Type} (P : A -> B -> C -> D -> E -> Prop) : Type :=
  exist_5var : forall x y z t w, P x y z t w -> sig5var P.

(* These definitions extend proj1_sig and proj2_sig to the new types.*)
Definition proj1_sig2var {A B P} (e : @sig2var A B P) :=
  match e with
    | exist_2var x y _ => P x y
  end.
Definition proj2_sig2var {A B P} (e : @sig2var A B P) : (proj1_sig2var e) :=
  match e with
    | exist_2var _ _ H => H
  end.

Definition proj1_sig3var {A B C P} (e : @sig3var A B C P) :=
  match e with
    | exist_3var x y z _ => P x y z
  end.
Definition proj2_sig3var {A B C P} (e : @sig3var A B C P) : (proj1_sig3var e) :=
  match e with
    | exist_3var _ _ _ H => H
  end.

Definition proj1_sig4var {A B C D P} (e : @sig4var A B C D P) :=
  match e with
    | exist_4var x y z t _ => P x y z t
  end.
Definition proj2_sig4var {A B C D P} (e : @sig4var A B C D P) : (proj1_sig4var e) :=
  match e with
    | exist_4var _ _ _ _ H => H
  end.

Definition proj1_sig5var {A B C D E P} (e : @sig5var A B C D E P) :=
  match e with
    | exist_5var x y z t w _ => P x y z t w
  end.
Definition proj2_sig5var {A B C D E P} (e : @sig5var A B C D E P) : (proj1_sig5var e) :=
  match e with
    | exist_5var _ _ _ _ _ H => H
  end.

(* With H a term of type sig or sig_nvar, this tactic adds the applied
   term 'P x .. y' used to construct H to the list of hypotheses *)
Ltac assert_proj2 H :=
  let Name := fresh "H" in
  match type of H with
    | sig _ => assert (Name := proj2_sig H); simpl in Name
    | sig2var _ => assert (Name := proj2_sig2var H); simpl in Name
    | sig3var _ => assert (Name := proj2_sig3var H); simpl in Name
    | sig4var _ => assert (Name := proj2_sig4var H); simpl in Name
    | sig5var _ => assert (Name := proj2_sig5var H); simpl in Name
    | _ => fail "Argument does not have type sig or sig_nvar"
  end.

(* We extend the sig notation to the new types.*)
Notation "{ x , y | P }" :=
  (sig2var (fun x y => P)) : type_scope.
Notation "{ x , y , z | P }" :=
  (sig3var (fun x y z => P)) : type_scope.
Notation "{ x , y , z , t | P }" :=
  (sig4var (fun x y z t => P)) : type_scope.
Notation "{ x , y , z , t , w | P }" :=
  (sig5var (fun x y z t w => P)) : type_scope.
(* Explicit types *)
Notation "{ x : A , y : B | P }" :=
  (sig2var (fun (x : A) (y : B) => P)) : type_scope.
Notation "{ x : A , y : B , z : C | P }" :=
  (sig3var (fun (x : A) (y : B) (z : C) => P)) : type_scope.
Notation "{ x : A , y : B , z : C , t : D | P }" :=
  (sig4var (fun (x : A) (y : B) (z : C) (t : D) => P)) : type_scope.
Notation "{ x : A , y : B , z : C , t : D , w : E | P }" :=
  (sig5var (fun (x : A) (y : B) (z : C) (t : D) (w : E) => P)) : type_scope.