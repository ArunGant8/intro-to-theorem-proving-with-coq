(* My First Proof!
   We will prove the proposition:
   "for all things you could prove,
   if you have a proof of it, then you have a proof of it." *)

Theorem my_first_proof: (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

