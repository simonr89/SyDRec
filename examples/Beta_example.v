Require Import SyDRec.Constructive.

Lemma exists_f :
  exists f, forall n, f n = n + n.
Proof.
  eapply ex_intro.
  intros n.
  beta.
  reflexivity.
Qed.

Lemma nexists_g :
  exists g, forall n m, g n = n + m.
Proof.
  eapply ex_intro.
  intros n m.
  beta.
  (* Here the expression of g depends on variable m, so reflexivity
     cannot prove the goal*)
Abort.

(* The beta module also provides definitions and tactics to construct
   and use existential definitions constructively. This was in
   particular intended to construct functions, but here is a more
   general example.*)

Open Scope instance_scope.

Definition tuple_plus_instance :
  instance a, b of (a > b).
Proof.
  einstance. (* eapply on the appropriate constructor *)
  instantiate (1 := 2).
  instantiate (1 := 5).
  auto.
Defined.

(* To reuse the instance we just constructed, we use the tactic
   assert_instance, which asserts a projection of a term of type
   sig_nvar. This projection allows us to get back the instances we
   provided to define the term.*)
Lemma tuple_plus :
  5 > 2.
Proof.
  assert_instance tuple_plus_instance.
  exact H.
Qed.
(* For more interesting uses of these types and tactics, see the BMF
   module documentation. *)