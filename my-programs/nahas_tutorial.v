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

(* Something a bit more complicated: *)

Theorem forward_small : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
  intros A.
  intros B.
  intros proof_of_A.
  intros A_implies_B.
  pose (proof_of_B := A_implies_B proof_of_A).  (* used in forward proofs *)
  exact proof_of_B.
Qed.

(* Proof going backward *)

Theorem backward_small : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
  intros A B.
  intros proof_of_A A_implies_B.
  refine (A_implies_B _).
  exact proof_of_A.
Qed.

