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

(* True and False (better named Provable and Unprovable) *)
(* True is provable *)

Theorem True_can_be_proven : True.
  exact I.
Qed.

(* False is unprovable *)

Theorem False_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.


(* Reductio ad Absurdum *)

Theorem absurd2 : forall A C : Prop, A -> ~A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
Qed.

Require Import Bool.

(* true is True (i.e. provable) *)

Theorem true_is_True: Is_true true.
Proof.
  simpl.     (* simplify *)
  exact I.
Qed.

(* Is_true called with a complex argument *)

Theorem not_eqb_true_false : ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_cannot_be_proven.
Qed.

(* case with bools *)

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.

  (* suppose a is true *)
  simpl.
  exact I.

  (* suppose a is false *)
  simpl.
  exact I.

Qed.

(* another example of the previous type *)

Theorem thm_eqb_a_t : (forall a: bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.

  (* suppose a is true *)
  simpl.
  intros proof_of_True.
  exact I.

  (* suppose a is false *)
  simpl.
  intros proof_of_False.
  case proof_of_False.

Qed.

(* Or: a function with the signature
  or (A B : Prop) : Prop            *)

Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B). (* NOTE: We need to specify the type A \/ B since
                                                             Coq cannot infer the type B of the OR simply
                                                             from the given information *)
  exact proof_of_A_or_B.
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  refine (or_intror _).
  exact proof_of_B.
Qed.

(* Or commutes *)

Theorem or_commutes : (forall A B : Prop, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.

  (* suppose A_or_B is (or_introl proof_of_A). *)
  intros proof_of_A.
  refine (or_intror _).
  exact proof_of_A.

  (* suppose A_or_B is (or_intror proof_of_B). *)
  intros proof_of_B.
  refine (or_introl _).
  exact proof_of_B.

Qed.

(* AND: has a single constructor, as opposed to OR,
   which has two                                   *)

Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  pose (proof_of_A_and_B := conj proof_of_A proof_of_B).
  exact proof_of_A_and_B.
Qed.

(* AND commutes *)

Theorem and_commutes : (forall A B : Prop, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  case A_and_B.

  (* suppose A_and_B is (conj proof_of_A proof_of_B). *)
  intros proof_of_A proof_of_B.
  refine (conj _ _).

  exact proof_of_B.    (* subgoal 1 *)

  exact proof_of_A.    (* subgoal 2 *)

Qed.

(* destruct tactic
   (Recommended) Usage:
   destruct <hyp> as [ <arg1> <arg2> ... ]. *)

Theorem and_commutes__again: (forall A B : Prop, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  destruct A_and_B as [ proof_of_A proof_of_B ].
  refine (conj _ _).

  exact proof_of_B.

  exact proof_of_A.

Qed.

(* orb is or: orb is the function defined in Bool
   that operates on bools and returns their OR. *)

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).

  (* orb -> \/ *)
  intros H.
  case a, b.

  (* suppose a, b is true, true *)
  simpl.
  refine (or_introl _).
  exact I.

  (* suppose a, b is true, false *)
  simpl.
  refine (or_introl _).
  exact I.

  (* suppose a, b is false, true *)
  simpl.
  refine (or_intror _).
  exact I.

  (* suppose a, b is false, false *)
  simpl in H.
  case H.

  (* \/ -> orb *)
  intros H.
  case a, b.

  (* suppose a, b is true, true *)
  simpl.
  exact I.

  (* suppose a, b is true, false *)
  simpl.
  exact I.

  (* suppose a, b is false, true *)
  simpl.
  exact I.

  (* suppose a, b is false, false *)
  case H.

  (* suppose H is (or_introl A). *)
  intros A.
  simpl in A.
  case A.

  (* suppose H is (or_intror B). *)
  intros B.
  simpl in B.
  case B.

Qed.

(* andb is /\ *)

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).

  (* andb -> /\ *)
  intros H.
  case a, b.

  (* suppose a, b is true, true *)
  simpl.
  exact (conj I I).

  (* suppose a, b is true, false *)
  simpl in H.
  case H.

  (* suppose a, b is false, true *)
  simpl in H.
  case H.

  (* suppose a, b is false, false *)
  simpl in H.
  case H.

  (* /\ -> andb *)
  intros H.
  case a, b.

  (* suppose a, b is true, true *)
  simpl.
  exact I.

  (* suppose a, b is true, false *)
  simpl in H.
  destruct H as [ A B ].
  case B.

  (* suppose a, b is false, true *)
  simpl in H.
  destruct H as [ A B ].
  case A.

  (* suppose a, b is false, false *)
  simpl in H.
  destruct H as [ A B ].
  case A.

Qed.

(* negb is NOT *)

Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros a.
  unfold iff.
  refine (conj _ _).

  (* negb -> NOT *)
  intros H.
  simpl.
  admit.
  admit.
Admitted.

(* Existence:
   In Coq, you cannot just declare that
   something exists. You have to prove it,
   in the form of a "witness" of its existence. *)

Definition basic_predicate :=
  (fun a => Is_true (andb a true)).

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
  simpl.
  exact I.
Qed.

Theorem thm_exists_basics__again : (exists a, Is_true (andb a true)).
Proof.
  pose (witness := true).
  refine (ex_intro _ witness _).
  simpl.
  exact I.
Qed.

(* Existence and Universality, combined *)

Theorem thm_forall_exists : (forall b, (exists a, Is_true (eqb a b))).
Proof.
  intros b.
  case b.

  (* b is true *)
  pose (witness := true).
  refine (ex_intro _ witness _).
  simpl.
  exact I.

  (* b is false *)
  pose (witness := false).
  refine (ex_intro _ witness _).
  simpl.
  exact I.

Qed.

(* The witness is always equal to b in the above proof.
   So we can simplify it *)

Theorem thm_forall_exists__again : (forall a, (exists b, Is_true (eqb a b))).
Proof.
  intros b.
  refine (ex_intro _ b _).
  exact (eqb_a_a b).
Qed.

(* Exists and Forall *)

Theorem forall_exists : (forall P : Set -> Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P.
  intros forall_x_not_Px.
  unfold not.
  intros exists_x_Px.
  destruct exists_x_Px as [ witness proof_of_Pwitness ].
  pose (not_Pwitness := forall_x_not_Px witness).
  unfold not in not_Pwitness.
  pose (proof_of_False := not_Pwitness proof_of_Pwitness).
  case proof_of_False.
Qed.

(* Now for the other way *)

Theorem exists_forall : (forall P : Set -> Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
  intros P.
  intros not_exists_x_Px.
  intros x.
  unfold not.
  intros P_x.
  unfold not in not_exists_x_Px.
  refine (not_exists_x_Px _).
  exact (ex_intro P x P_x).
Qed.


(* Equality
   Has only one constructor, eq_refl *)

(* Equality is symmetric *)

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
  intros x y.
  intros x_y.
  destruct x_y as [].
  exact (eq_refl x).
Qed.

(* Equality is transitive *)

Theorem thm_eq_trans : (forall x y z : Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  destruct x_y as [].
  exact y_z.
Qed.

(* rewrite and rewrite <- *)

Theorem thm_eq_trans__again : (forall x y z : Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  rewrite x_y.
  rewrite <- y_z.
  exact (eq_refl y).
Qed.

(* An example that explicitly relies on convertibility *)

(* andb is symmetric *)

Theorem andb_sym : (forall a b, a && b = b && a).
Proof.
  intros a b.
  case a, b.

  (* suppose a, b is true, true *)
  simpl.
  exact (eq_refl true).

  (* suppose a, b is true, false *)
  simpl.
  exact (eq_refl false).

  (* suppose a, b is false, true *)
  simpl.
  exact (eq_refl false).

  (* suppose a, b is false, false *)
  simpl.
  exact (eq_refl false).

Qed.

(* Inequality with discriminate *)

Theorem neq_nega : (forall a, a <> (negb a)).
Proof.
  intros a.
  unfold not.
  case a.

  (* a is true *)
  intros a_eq_neg_a.
  simpl in a_eq_neg_a.
  discriminate a_eq_neg_a.

  (* a is false *)
  intros a_eq_neg_a.
  simpl in a_eq_neg_a.
  discriminate a_eq_neg_a.

Qed.

(* Natural Numbers *)

(* Natural numbers are:
    | O (zero, written with the alphabet O
    | (S n), where n is a natural number
*)

Theorem plus_2_3 : (S (S O)) + (S (S (S O))) = (S (S (S (S (S O))))).
Proof.
  simpl.
  exact (eq_refl 5).
Qed.

(* Induction *)

Check nat_ind.  (* Automatically generated induction scheme for nats *)

(* n + 0 = n *)

Theorem plus_n_0 : (forall n, n + 0 = n).
Proof.
  intros n.
  elim n.     (* very similar to case, but automatically generates
                 the induction goals *)

  (* base case: *)
  simpl.
  exact (eq_refl 0).

  (* inductive case *)
  intros n0.
  intros inductive_hypothesis.
  simpl.
  rewrite inductive_hypothesis.
  exact (eq_refl (S n0)).
Qed.

(* induction tactic *)

Theorem plus_n_0__again : (forall n : nat, n + 0 = n).
Proof.
  intros n.
  induction n as [ | n0 inductive_hypothesis ].

  (* base case *)
  simpl.
  exact (eq_refl 0).

  (* inductive case *)
  simpl.
  rewrite inductive_hypothesis.
  exact (eq_refl (S n0)).

Qed.

(* Commands to display definitions *)
Print or.
Print nat_ind.

(* Addition is Symmetric *)

Theorem plus_sym : (forall n m : nat, n + m = m + n).
Proof.
  intros n m.
  elim n.

  (* base case for n *)
  elim m.

  (* base case for m *)
  simpl.
  exact (eq_refl 0).

  (* inductive case for m *)
  intros n0 inductive_hypothesis_m.
  simpl.
  rewrite <- inductive_hypothesis_m.
  simpl.
  exact (eq_refl (S n0)).

  (* inductive hypothesis for n *)
  intros n0 inductive_hypothesis_n.
  simpl.
  rewrite inductive_hypothesis_n.
  elim m.

  (* base case for m *)
  simpl.
  exact (eq_refl (S n0)).

  (* inductive case for m *)
  intros n1 inductive_hyp_m.
  simpl.
  rewrite inductive_hyp_m.
  simpl.
  exact (eq_refl (S (n1 + S n0))).

Qed.

(** DATA TYPES **)

Require Import List.

