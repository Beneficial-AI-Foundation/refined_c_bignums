From refinedc.typing Require Import typing.


Open Scope nat_scope.
(* Convert a list of bits (LSB first) to a natural number *)
Definition bits_to_nat (bits : list Z) : nat :=
  fold_right (fun b acc => Z.to_nat b + 2 * acc) 0 (rev bits).


(* Partial sum correctness for the first i digits *)
Definition partial_sum_correct (i : nat) (carry : Z) (bits_result : list Z)
                              (bits_a bits_b : list Z) :=
    (bits_to_nat (take i bits_a) + bits_to_nat (take i bits_b)) =
    bits_to_nat (take i bits_result) + Z.to_nat carry * 2^i.


Close Scope nat_scope.

(* Check if all elements are binary (0 or 1) *)
Definition is_binary (bits : list Z) := 
  Forall (fun b => b = 0 ∨ b = 1) bits.







Lemma binary_sum_within_i32_bounds (bits_a bits_b : list Z) (i : nat) (y y0 : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i = Some y →
  bits_b !! i = Some y0 →
  y + y0 <= max_int i32.
Proof. Admitted.


Lemma partial_sum_step_exact (bits_a bits_b : list Z) (n : Z) (initial_result : list Z)
                            (i_val : nat) (carry_val : Z) (current_result : list Z)
                            (y y0 y1 : Z) :
  is_binary bits_a →
  is_binary bits_b →
  carry_val = 0 ∨ carry_val = 1 →
  partial_sum_correct i_val carry_val current_result bits_a bits_b →
  i_val < n →
  bits_a !! i_val = Some y →
  bits_b !! i_val = Some y0 →
  current_result !! i_val = Some y1 →
  partial_sum_correct (i_val + 1) ((y + y0 + carry_val) `quot` 2)
    (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result) bits_a bits_b.
Proof. Admitted.

Lemma partial_sum_complete (i : nat) (carry_val : Z) (bits_result : list Z)
                          (bits_a bits_b : list Z) (n : Z) :
  i ≤ n →
  ¬ i < n →
  partial_sum_correct i carry_val bits_result bits_a bits_b →
  bits_to_nat (<[Z.to_nat n:=carry_val]> bits_result) = Z.to_nat (bits_to_nat bits_a + bits_to_nat bits_b).
Proof. Admitted.

Lemma binary_sum_min_bound (bits_a bits_b : list Z) (i : nat) (y y0 : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i = Some y →
  bits_b !! i = Some y0 →
  min_int i32 ≤ y + y0.
Proof. Admitted.

Lemma binary_sum_with_carry_bound (bits_a bits_b : list Z) (i : nat) (y y0 carry_val : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i = Some y →
  bits_b !! i = Some y0 →
  (carry_val = 0 ∨ carry_val = 1) →
  y + y0 + carry_val ≤ max_int i32.
Proof. Admitted.


Lemma binary_add_quot (bits_a bits_b : list Z) (i : nat) (y y0 carry_val : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i = Some y →
  bits_b !! i = Some y0 →
  (carry_val = 0 ∨ carry_val = 1) →
  (y + y0 + carry_val) `quot` 2 = 0 ∨ (y + y0 + carry_val) `quot` 2 = 1.
Proof.
  intros Hbinary_a Hbinary_b Hlookup_a Hlookup_b Hcarry.
  unfold is_binary in Hbinary_a, Hbinary_b.
  apply Forall_lookup with (i:=i) (x:=y) in Hbinary_a; auto.
  apply Forall_lookup with (i:=i) (x:=y0) in Hbinary_b; auto.
  destruct Hbinary_a as [Hy0 | Hy1]; destruct Hbinary_b as [Hy00 | Hy01]; destruct Hcarry as [Hc0 | Hc1]; subst.
  - left. simpl. reflexivity.
  Show. Qed.

Lemma binary_sum_non_negative (bits_a bits_b : list Z) (i : nat) (y y0 carry_val : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i = Some y →
  bits_b !! i = Some y0 →
  (carry_val = 0 ∨ carry_val = 1) →
  0 ≤ y + y0 + carry_val.
Proof.
  intros Hbinary_a Hbinary_b Hlookup_a Hlookup_b Hcarry.
  unfold is_binary in Hbinary_a, Hbinary_b.
  apply Forall_lookup with (i:=i) (x:=y) in Hbinary_a; auto.
  apply Forall_lookup with (i:=i) (x:=y0) in Hbinary_b; auto.
  destruct Hbinary_a as [Hy0 | Hy1]; destruct Hbinary_b as [Hy00 | Hy01]; destruct Hcarry as [Hc0 | Hc1]; subst; lia.
  Qed.


Lemma binary_update_preserves_binary (current_result : list Z) (i_val : nat) (bits_a bits_b : list Z) (y y0 carry_val : Z) (n : Z) :
  is_binary (take i_val current_result) →
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i_val = Some y →
  bits_b !! i_val = Some y0 →
  (carry_val = 0 ∨ carry_val = 1) →
  (0 ≤ i_val) →
  (i_val ≤ n) →
  (length current_result = Z.to_nat (n + 1)) →
  is_binary (take (i_val + 1) (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result)).
Proof.
  intros Hbinary_curr Hbinary_a Hbinary_b Hlookup_a Hlookup_b Hcarry Hi_val_lower Hi_val_upper Hlength.
  unfold is_binary.
  apply Forall_forall.
  intros x Hin.
  apply elem_of_list_lookup in Hin as [j Hj].
  assert (j < i_val + 1)%nat as Hj_bound.
  - assert (j < length (take (i_val + 1) (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result)))%nat by (apply lookup_lt_Some in Hj; auto).
    rewrite length_take in H.
    destruct (decide ((i_val + 1) <= length (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result))%nat) as [Hle|Hnle].
    + rewrite Nat.min_l in H; lia.
    + rewrite Nat.min_r in H; try lia.
  - (* Case: j = i_val *)
    destruct (decide (j = i_val)) as [Heq|Hneq].
    + subst j.
      rewrite lookup_take in Hj; try lia.
      rewrite list_lookup_insert in Hj; try lia.
    -- injection Hj as Hj; subst x.
      assert (0 <= (y + y0 + carry_val) `rem` 2 < 2) as Hrem.
      { 
        apply Z.rem_bound_pos.
        - apply binary_sum_non_negative with (bits_a:=bits_a) (bits_b:=bits_b) (i:=i_val); auto.
        - lia. (* 2 > 0 *)
      }
      destruct Hrem as [Hrem_lower Hrem_upper].
      assert ((y + y0 + carry_val) `rem` 2 = 0 ∨ (y + y0 + carry_val) `rem` 2 = 1) as H.
      {
        destruct (Z.eq_dec ((y + y0 + carry_val) `rem` 2) 0).
        - left; auto.
        - right.
          assert ((y + y0 + carry_val) `rem` 2 = 1) by lia.
          auto.
      }
      exact H.
    + (* Case: j ≠ i_val *)
      rewrite lookup_take in Hj; try lia.
      rewrite list_lookup_insert_ne in Hj; auto.
      unfold is_binary in Hbinary_curr.
      assert (j < i_val)%nat by lia.
      assert (take i_val current_result !! j = Some x) as Htake.
      { rewrite lookup_take; auto. }
      apply (Forall_lookup_1 _ _ _ _ Hbinary_curr Htake).
Qed.

Lemma carry_update_preserves_binary (current_result : list Z) (i_val : nat) (n : Z) (carry_val : Z) :
  is_binary (take i_val current_result) →
  (carry_val = 0 ∨ carry_val = 1) →
  i_val ≤ n →
  ¬ i_val < n →
  (length current_result = Z.to_nat (n + 1)) ->
  is_binary (<[Z.to_nat n:=carry_val]> current_result).
Proof.
  intros Hbinary Hcarry Hle Hnlt Hlength.
  unfold is_binary.
  apply Forall_forall.
  intros x Hin.
  apply elem_of_list_lookup in Hin as [i Hi].
  destruct (decide (i = Z.to_nat n)) as [Heq|Hneq].
  * (* Case: i = Z.to_nat n *)
    subst i.
    rewrite list_lookup_insert in Hi.
    + injection Hi as Hi; subst x; exact Hcarry.
    + rewrite Hlength.
      rewrite Z2Nat.inj_add; try lia.
  * (* Case: i ≠ Z.to_nat n *)
    rewrite list_lookup_insert_ne in Hi; auto.
    destruct (decide (i < i_val)%nat) as [Hlt|Hnlt'].
    + (* i < i_val *)
      unfold is_binary in Hbinary.
      assert (take i_val current_result !! i = Some x) as Htake.
      { rewrite lookup_take; auto. }
      apply (Forall_lookup_1 _ _ _ _ Hbinary Htake).
    + (* i ≥ i_val *)
      exfalso.
      assert (i < Z.to_nat n)%nat.
      { apply (lookup_lt_Some current_result i x) in Hi.
        rewrite Hlength in Hi.
        destruct (decide (i < Z.to_nat n)%nat); auto.
        assert (i = Z.to_nat n) by lia. contradiction. }
      assert (i_val ≤ i)%nat by lia.
      apply Hnlt. lia.
  Qed.

Lemma initial_partial_sum_correct :
  ∀ bits_a bits_b bits_result,
  is_binary bits_a →
  is_binary bits_b →
  partial_sum_correct 0 0 bits_result bits_a bits_b.
Proof.
  intros bits_a bits_b bits_result _ _.
  unfold partial_sum_correct.
  simpl.
  (* At position 0, take 0 returns empty list *)
  rewrite !take_0.
  (* bits_to_nat of empty list is 0 *)
  simpl.
  (* 0 + 0 = 0 *)
  reflexivity.
Qed.
