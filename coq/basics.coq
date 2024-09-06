Inductive bool : Type :=
  | true
  | false.

(* !b *)
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Compute (negb false).

(* a && b *)
Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Compute (andb false false).

(* a || b *)
Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Print the type of an expression *)
Check negb.

Module InventingNumbers.

(* We don't even have numbers yet, let's invent some *)
Inductive number : Type :=
  | None
  | Next (n : number).

(* Writing ||| on our cave wall as we count mammoths going by *)
Check (Next (Next (Next (None)))).

(* Normally defined as _natural_ numbers: *)
Inductive nat : Type :=
  | O
  | S (n : nat).

Check (S (S (S (S (S O))))).

End InventingNumbers.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S O))).

Compute (minustwo 4).

(* Coq is a proof assistant, let's prove something *)
Theorem add_0_is_idempotent : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.