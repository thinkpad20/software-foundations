Theorem succ_injective: forall (n m: nat), 
  S n = S m -> n = m.
Proof.
  intros. induction n as [|n']. 
    inversion H. reflexivity.
    inversion H. reflexivity.
Qed.

Definition injective {A B: Type} (f: A -> B) : Prop :=
  forall (a b: A), f a = f b -> a = b.

Definition surjective {A B: Type} (f: A -> B) : Prop :=
  forall (b: B), exists (a: A), f a = b.

Definition right_inverse {A B: Type} (f: A -> B): Prop :=
  exists (g: B -> A), (forall (a: A), g (f a) = a).

Check injective.

Theorem succ_inj : injective S.
Proof. 
  unfold injective. 
  intros. destruct a as [|k].
  inversion H. reflexivity.
  inversion H. reflexivity.
Qed.

Theorem injective_implies_right_inverse:
  forall (A B: Type) (f: A -> B), injective f -> right_inverse f.
Proof.
  unfold right_inverse. intros A B f inject.
  unfold injective in inject.
Admitted.

(*Theorem injective_right_inverse: 
  forall (A B: Type) (f: A -> B),
  Injective f <-> RightInverse f.
Proof.
  intros.
  split.
Admitted.*)

Require Import List.

Theorem rev_injective : forall (T: Type), injective (rev (A:=T)).
Proof.
  unfold injective. intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

