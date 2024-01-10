From Coq Require Import List.
Import ListNotations. 

Lemma gautham_exercise: forall (p: Prop), ~~ (p \/ ~p). 
Proof.
  intros p H.
  apply H.
  right.
  intros Hp.
  apply H.
  left.
  apply Hp. 
Qed.

(* Find f such that foldl f id l [] = reverse l
   Answer : f g x = fun l => x::g l *)

Fixpoint reverse {A: Type} (l: list A) : list A
  := match l with
     | [] => []
     | x::xs => reverse xs ++ [x] end.

Fixpoint revInto {A: Type} (l acc: list A) : list A 
  := match l with
     | [] => acc
     | x::xs => revInto xs (x::acc) end.

Definition fastrev {A:Type} (l: list A) : list A
  := revInto l [].

Lemma revInto_correct: forall (A: Type) (l acc : list A), revInto l acc = reverse l ++ acc.
Proof.
  intros A.
  induction l as [ | h t IH]. - intros l'. reflexivity.
  - intros l'.
    simpl.
    rewrite <- app_assoc.
    simpl.
    apply IH. 
Qed.

Lemma fastrev_correct: forall (A:Type) (l : list A), reverse l = fastrev l. 
Proof.
  intros A l.
  unfold fastrev.
  symmetry.
  rewrite <- app_nil_r.
  apply revInto_correct. 
Qed.


Fixpoint foldl {A B: Type} (f : B -> A -> B) (val : B) (l : list A) : B 
  := match l with
     | [] => val
     | x::xs => foldl f (f val x) xs end.


Definition f {A: Type} (g : list A -> list A) (x: A) (l : list A) : list A := x::g l.

Definition id {A: Type} := fun (x:A) => x.

Lemma funny_fold_gen_exercise :
  forall (A: Type) (l l' : list A) (h : list A -> list A), foldl f h l l' = revInto l (h l').
Proof.
  admit.
Admitted. 

Lemma funny_fold_exercise : forall (A: Type) (l : list A), foldl f id l [] = reverse l.
Proof.
  admit.
Admitted.
