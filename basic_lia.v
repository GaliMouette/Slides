Require Import Lia.

Lemma add_zero : forall x : nat, x + 0 = x.
Proof.
  intros x.
  lia.
Qed.
