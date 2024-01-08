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

(* Proof going backward (Large) *)

Theorem backward_large : (forall A B C : Prop, A -> (A -> B) -> (B -> C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B B_implies_C.
  refine (B_implies_C _).
  refine (A_implies_B _).
  exact proof_of_A.
Qed.

(* Proof going backward (HUGE) *)

Theorem backward_huge : (forall A B C : Prop, A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B A_implies_B_implies_C.
  refine (A_implies_B_implies_C _ _).
  exact proof_of_A.

  refine (A_implies_B _).
  exact proof_of_A.
Qed.

(* Proof going forward (HUGE) *)

Theorem forward_huge : (forall A B C : Prop, A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B A_implies_B_implies_C.
  pose (proof_of_B := A_implies_B proof_of_A).
  pose (proof_of_C := A_implies_B_implies_C proof_of_A proof_of_B).
  exact proof_of_C.
  Show Proof.
Qed.
