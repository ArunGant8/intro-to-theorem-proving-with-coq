
(* Lecture 2: Examples taken from
   Basics.v of software foundations *)

Module NatPlayground.



Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S m => S m * fact m
  end.

Check 5 = 6.

Fixpoint eqb (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S k, S l => (eqb k l)
  end.

Check eqb 5 6. (* bool *)

Lemma negb_involutive : forall b : bool, (negb (negb b)) = b.
Proof.
  intros [ | ].
  - reflexivity.  (* this is like eq_refl, but on steroids. *)
  - reflexivity.
Qed.

Lemma triple_involution :
  forall (f : bool -> bool) (b : bool), f (f (f b)) = f b.
Proof.
  admit.
Admitted.


End NatPlayground.
