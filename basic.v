Lemma add_zero : forall x : nat, x + 0 = x.
Proof.
  intros x.
  induction x as [| x' IHx'].
    simpl. reflexivity.
    simpl. rewrite IHx'. reflexivity.
Qed.
