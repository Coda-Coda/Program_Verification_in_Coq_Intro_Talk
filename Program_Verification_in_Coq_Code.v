(** CoqIde can be downloaded from https://coq.inria.fr/download and can be used to step through the proofs in this file interactively. *)

(** * Example: Plus *)

Module example.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

(** Example above from: Software Foundations Textbook. (https://softwarefoundations.cis.upenn.edu/) *)

End example.

Extraction Language Haskell.

Extraction example.

(** * Example: Even Numbers *)
  
(** ** Example: Even numbers - 'How' *)

Fixpoint evenb (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n) => evenb n
end.

(** ** Example: Even numbers - 'What' *)

Definition Even (n : nat) : Prop :=
exists m, n = 2 * m.

(** ** Example: Even numbers - 'Correctness' *)

Lemma evenb_correct : forall n, evenb n = true <-> Even n. 
Abort. (** Proved below. *)

(** ** Example: Even numbers - 'Why' *)

Lemma lemma_one : forall n, evenb (S n) = negb (evenb n).
Proof.
induction n as [|n'].
 - (** Base case: [n = 0] *)

   reflexivity.
 - (** Inductive case: for some [n'], [n = S n'] *)

   rewrite IHn'. simpl.
   destruct (evenb n') eqn:SubCase. 
     + (** Sub-case [(evenb n') = true] *) 

        reflexivity. 
     + (** Sub-case [(evenb n') = false] *) 

        reflexivity.
Qed.

(** ** Example: Even numbers - 'Why' *)

Require Import Classical.

Lemma lemma_two : forall n, Even (S n) <-> ~ Even n.
Proof.
split. 
 - induction n as [|n']. 
     + (** Base case: [n = 0]: *)
        unfold Even. intros. destruct H. destruct x. inversion H. simpl in H. rewrite <- plus_n_Sm in H. discriminate H.
     + (** Inductive case: for some [n'], [n = S n']: *)
        intros. unfold not. intros. apply IHn'. exact H0. unfold Even. destruct H. destruct x. simpl in H. discriminate H. exists x. simpl in H. rewrite <- plus_n_Sm in H. inversion H. simpl. reflexivity.
 - induction n. intros. unfold Even in H. exfalso. apply H. exists 0. reflexivity.
 intros. apply NNPP. unfold not. intros. apply H. apply IHn. unfold not. intros. apply H0. unfold Even in H. destruct H1. unfold Even. exists (S x). rewrite H1. simpl. rewrite <- plus_n_Sm. reflexivity. Qed.

(** ** Example: Even numbers - 'Why' *)

Lemma evenb_correct : forall n, evenb n = true <-> Even n.
Proof.
induction n.
 - firstorder. unfold Even. exists 0. reflexivity.
 - split.
    + intros. rewrite -> lemma_one in H. rewrite lemma_two. unfold not. intros. apply IHn in H0. rewrite H0 in H. simpl in H. discriminate H.
    + intros. apply lemma_two in H. rewrite lemma_one. destruct (evenb n) eqn:Case.
        * exfalso. apply H. apply IHn. reflexivity.
        * reflexivity.
Qed.

(** ** Example: Even numbers - 'What+How' *)


Program Definition evenb' 
   (n : nat) : {b:bool | b = true <-> Even n} := 
match n with
| 0 => true
| 1 => false
| S (S n) => evenb n
end.

(** ** Example: Even numbers - 'Why' *)

Next Obligation.
firstorder. exists 0. reflexivity. Qed.
Next Obligation.
firstorder. inversion H. destruct x. inversion H. simpl in H. rewrite <- plus_n_Sm in H. inversion H. Qed.
Next Obligation.
induction n.
 - firstorder. unfold Even. exists 1. reflexivity.
 - split.
    + intros. rewrite -> lemma_one in H. rewrite lemma_two. unfold not. intros. apply IHn in H0. rewrite H0 in H. simpl in H. discriminate H.
    + intros. apply lemma_two in H. rewrite lemma_one. destruct (evenb n) eqn:Case.
        * exfalso. apply H. apply IHn. reflexivity.
        * reflexivity.
Qed.

(** * Software Foundations
https://softwarefoundations.cis.upenn.edu/
*)

(** * Related *)
(** 
 - VellVM http://www.cis.upenn.edu/~stevez/vellvm/
 - CompCert http://compcert.inria.fr/
 - Spark Ada (e.g. Air traffic management systems) http://www.adacore.com/sparkpro/
 - Model Checking
*)

(** * DeepSpec *)
(** 
https://deepspec.org/
%*)