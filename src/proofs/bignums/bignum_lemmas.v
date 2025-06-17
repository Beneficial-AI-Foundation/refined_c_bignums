From refinedc.typing Require Import typing.

(* Convert a list of bits (LSB first) to a natural number *)
Definition bits_to_nat (bits : list Z) : nat :=
  let fix go (i:nat) l :=
    match l with
    | [] => Z.to_nat 0
    | b :: bs => (Z.to_nat (b * 2^i) + Z.to_nat (go (i-1) bs))%nat
    end
  in go (length bits - 1)%nat (rev bits).

Open Scope nat_scope.


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
Proof.
  intros Hbinary_a Hbinary_b Hlookup_a Hlookup_b.
  unfold is_binary in Hbinary_a, Hbinary_b.
  apply Forall_lookup with (i:=i) (x:=y) in Hbinary_a; auto.
  apply Forall_lookup with (i:=i) (x:=y0) in Hbinary_b; auto.
  
  (* Since y and y0 are binary digits (0 or 1), their sum is at most 2 *)
  assert (y + y0 <= 2) by (
    destruct Hbinary_a, Hbinary_b; subst; lia
  ).
  
  (* And 2 is certainly less than max_int i32 (which is at least 127) *)
  pose proof (max_int_ge_127 i32).
  lia.
Qed.


(* Lemma relating bits_to_nat of take (i+1) to bits_to_nat of take i *)
Lemma bits_to_nat_take_step (bits : list Z) (i : nat) (x : Z) :
  bits !! i = Some x →
  bits_to_nat (take (i + 1) bits) = (bits_to_nat (take i bits) + Z.to_nat (x * 2^i))%nat.
Proof.
  Admitted.

Lemma partial_sum_step_exact (bits_a bits_b : list Z) (n : Z) (initial_result : list Z)
                            (i_val : nat) (carry_val : Z) (current_result : list Z)
                            (y y0 y1 : Z) :
  is_binary bits_a →
  is_binary bits_b →
  carry_val = 0 ∨ carry_val = 1 →
  partial_sum_correct i_val carry_val current_result bits_a bits_b →
  i_val < n →
  length current_result = Z.to_nat (n+1) ->
  bits_a !! i_val = Some y →
  bits_b !! i_val = Some y0 →
  current_result !! i_val = Some y1 →
  partial_sum_correct (i_val + 1) ((y + y0 + carry_val) `quot` 2)
    (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result) bits_a bits_b.
Proof.
  intros.
  unfold partial_sum_correct.
  unfold partial_sum_correct in H2.
  
  (* Apply bits_to_nat_take_step to both sides of the goal *)
  rewrite (bits_to_nat_take_step bits_a i_val y); auto.
  rewrite (bits_to_nat_take_step bits_b i_val y0); auto.
  rewrite (bits_to_nat_take_step (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result) i_val ((y + y0 + carry_val) `rem` 2)).
  - rewrite (Nat.add_comm (bits_to_nat (take i_val bits_a)) (Z.to_nat (y * 2 ^ i_val))).
    rewrite Nat.add_assoc.
    rewrite <- (Nat.add_assoc (Z.to_nat _) (bits_to_nat _) (bits_to_nat _)).
    rewrite H2.
    assert (take i_val current_result = take i_val (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result)) as Ha by admit.
    rewrite <- Ha.
    assert ((Z.to_nat (y * 2 ^ i_val) +
      (bits_to_nat (take i_val current_result) + Z.to_nat carry_val * 2 ^ i_val) +
      Z.to_nat (y0 * 2 ^ i_val))%nat =
      (bits_to_nat (take i_val current_result) + (Z.to_nat (y * 2 ^ i_val) +
      Z.to_nat carry_val * 2 ^ i_val +
      Z.to_nat (y0 * 2 ^ i_val)))%nat) as Hb by lia.
    rewrite Hb.
    assert ((bits_to_nat (take i_val current_result) +
      Z.to_nat ((y + y0 + carry_val) `rem` 2 * 2 ^ i_val) +
      Z.to_nat ((y + y0 + carry_val) ÷ 2) * 2 ^ (i_val + 1))%nat =
      (bits_to_nat (take i_val current_result) +
      (Z.to_nat ((y + y0 + carry_val) `rem` 2 * 2 ^ i_val) +
      Z.to_nat ((y + y0 + carry_val) ÷ 2) * 2 ^ (i_val + 1)))%nat) as Hc by lia.
    rewrite Hc.
    apply Nat.add_cancel_l.
    assert ((Z.to_nat y + Z.to_nat carry_val  + Z.to_nat y0)%nat = (Z.to_nat ((y + y0 + carry_val) `rem` 2 ) + 2 * Z.to_nat ((y + y0 + carry_val) `quot` 2) )%nat).
    + assert (y0 = 0 ∨ y0 = 1) by admit.
      assert (y = 0 ∨ y = 1) by admit.
      destruct H1; destruct H8; destruct H9; lia.
    + assert ((Z.to_nat y * 2 ^ i_val = Z.to_nat (y * 2 ^ i_val))%nat) by admit.
      rewrite <- H9.
      assert ((Z.to_nat y0 * 2 ^ i_val = Z.to_nat (y0 * 2 ^ i_val))%nat) by admit.
      rewrite <- H10.
      assert ((Z.to_nat y * 2 ^ i_val + Z.to_nat carry_val * 2 ^ i_val +
   Z.to_nat y0 * 2 ^ i_val)%nat = ((Z.to_nat y + Z.to_nat carry_val +
   Z.to_nat y0 )* 2 ^ i_val)%nat ) by lia.
      rewrite H11.
  - admit.
Admitted.

(* Lemma showing that if the reverse of a list is empty, the list is empty *)
Lemma rev_empty_is_empty (l : list Z) :
  rev l = [] -> l = [].
Proof.
  intro H.
  apply rev_inj.
  rewrite H.
  reflexivity.
  Qed.

(* Lemma relating nat subtraction and Z.to_nat *)
Lemma length_minus_one_nat_z (l : list Z) :
  (length l - 1)%nat = Z.to_nat (length l - 1).
Proof.
  intros.
  rewrite Z2Nat.inj_sub.
  - lia.
  - lia.
Qed.


Lemma rev_insert_first' (len : nat) (carry_val : Z):
  forall lyst : list Z,
  length lyst = len ->
  rev (<[Z.to_nat (len - 1):=carry_val]> lyst) = <[0%nat:=carry_val]> (rev lyst).
Proof.
  induction len.
  - intros lyst1 H.
    assert (lyst1 = []) as H10.
    + apply length_zero_iff_nil. auto.
    + rewrite H10. auto.
  - intros lyst1 H.
    unfold rev.
    destruct lyst1.
    + auto.
    + destruct lyst1.
      -- simpl.
         assert (len = 0%nat) as H9.
         {simpl in H. lia. }
         rewrite H9.
         simpl.
         reflexivity.
      -- rewrite insert_app_l.
         ++ assert (((fix rev (l : list Z) : list Z :=
                      match l with
                      | [] => []
                      | x :: l' => rev l' ++ [x]
                      end) lyst1 ++ [z0]) = rev (z0 :: lyst1)) as H1 by auto.
            rewrite H1.
            specialize (IHlen (z0 :: lyst1)).
            assert (length (z0 :: lyst1) = len) as H2 by auto.
            specialize (IHlen H2).
            rewrite <- IHlen.
            assert ((fix rev (l : list Z) : list Z :=
                  match l with
                  | [] => []
                  | x :: l' => rev l' ++ [x]
                  end) (<[Z.to_nat (S len - 1):=carry_val]> (z :: z0 :: lyst1))
                       = rev (<[Z.to_nat (S len - 1):=carry_val]> (z :: z0 :: lyst1))) as H3.
            { unfold rev. reflexivity. }
            rewrite H3.
            assert (rev (<[Z.to_nat (len - 1):=carry_val]> (z0 :: lyst1)) ++ [z]
                   =  rev (z :: (<[Z.to_nat (len - 1):=carry_val]> (z0 :: lyst1)))) as H4.
            { unfold rev. reflexivity. }
            rewrite H4.
            f_equal.
            assert (z :: z0 :: lyst1 = [z] ++ (z0 :: lyst1)) as H5.
            {auto. }
            rewrite H5.
            assert ((length [z] + (len-1))%nat = Z.to_nat (S len - 1)) as H6.
            --- simpl.
                assert (len > 0) as H8.
                { destruct len; simpl in H; try discriminate. lia. }
                lia.
            --- rewrite <- H6.
                rewrite insert_app_r.
                assert ((len - 1)%nat = Z.to_nat (len - 1)) as H7 by lia.
                rewrite H7.
                simpl.
                reflexivity.
         ++ rewrite length_app.
            simpl.
            lia.
  Qed.

(* Lemma for relating rev and insertion *)
Lemma rev_insert_first (n : Z) (carry_val : Z) (bits_result : list Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  rev (<[Z.to_nat n:=carry_val]> bits_result) = <[0%nat:=carry_val]> (rev bits_result).
Proof.
  pose proof rev_insert_first'.
  specialize (H (Z.to_nat (n + 1)) carry_val bits_result).
  intros.
  assert (Z.to_nat (Z.to_nat (n + 1) - 1) = Z.to_nat n) as H2 by lia.
  rewrite H2 in H.
  auto.
  Qed.

(* Lemma relating length calculations for list indices *)
Lemma length_minus_one_equals_n (bits_result : list Z) (n : Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  (length bits_result - 1 - 1)%nat = (Z.to_nat n - 1)%nat.
Proof.
  intros.
  rewrite H.
  lia.
  Qed.

(* Lemma showing that length minus one equals n *)
Lemma length_minus_one_equals_n_simple (bits_result : list Z) (n : Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  (length bits_result - 1)%nat = Z.to_nat n.
Proof.
  intros.
  rewrite H.
  lia.
  Qed.

(* Lemma relating drop, rev and take *)
Lemma drop_rev_take (bits_result : list Z) (n : Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  drop 1 (rev bits_result) = rev (take (Z.to_nat n) bits_result).
Proof.
  intros.
  specialize (drop_reverse bits_result 1).
  intro H1.
  unfold reverse in H1.
  rewrite <- rev_alt in H1.
  rewrite <- rev_alt in H1.
  rewrite H1.
  rewrite H.
  f_equal.
  f_equal.
  lia.
  Qed.

(* Lemma relating bits_to_nat of rev and take *)
Lemma bits_to_nat_rev_take_eq (bits_result : list Z) (n : Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  Z.to_nat
    ((fix go (i : nat) (l0 : list Z) {struct l0} : nat :=
        match l0 with
        | [] => Z.to_nat 0
        | b :: bs => (Z.to_nat (b * 2 ^ i) + Z.to_nat (go (i - 1) bs))%nat
        end) (Z.to_nat n - 1)%nat (rev (take (Z.to_nat n) bits_result))) =
  (fix go (i : nat) (l0 : list Z) {struct l0} : nat :=
     match l0 with
     | [] => Z.to_nat 0
     | b :: bs => (Z.to_nat (b * 2 ^ i) + Z.to_nat (go (i - 1) bs))%nat
     end) (Z.to_nat n - 1)%nat (rev (take (Z.to_nat n) bits_result)).
Proof.
  intros.
  lia.
  Qed.

Lemma rearrange_nat (n carry_val: Z):
  n >= 0 ->
  (carry_val = 0 ∨ carry_val = 1) ->
  (Z.to_nat carry_val * 2 ^ Z.to_nat n)%nat = Z.to_nat (carry_val * 2 ^ Z.to_nat n).
Proof.
  intros.
  destruct H0.
  - rewrite H0.
    lia.
  - rewrite H0.
    assert (forall x : Z, 1 * x = x) as H1 by lia.
    specialize (H1 (2 ^ Z.to_nat n)).
    rewrite H1.
    assert (forall x : nat, (Z.to_nat 1 * x = x)%nat) as H2 by lia.
    specialize (H2 (2 ^ Z.to_nat n)%nat).
    rewrite H2.
    assert (2 = Z.to_nat 2) as H3 by lia.
    rewrite H3.
    rewrite <- Z2Nat.inj_pow.
    assert (2 = Z.to_nat 2)%nat as H4 by lia.
    rewrite <- H4.
    lia.
  Qed.

Lemma bits_to_nat_insert (n : Z) (carry_val : Z) (bits_result : list Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  (carry_val = 0 ∨ carry_val = 1) ->
  bits_to_nat (<[Z.to_nat n:=carry_val]> bits_result) = 
  (bits_to_nat (take (Z.to_nat n) bits_result) + Z.to_nat carry_val * 2 ^ Z.to_nat n)%nat.
Proof.
  intros Hlen Hn Hcarry.
  unfold bits_to_nat.
  rewrite length_insert.
  
  (* Use the lemma about rev and insertion *)
  assert (rev (<[Z.to_nat n:=carry_val]> bits_result) = <[0%nat:=carry_val]> (rev bits_result)) as Hrev_insert.
  { apply rev_insert_first; auto. }
  rewrite Hrev_insert.
  
  (* Expand the function definition *)
  assert (drop 1 (rev bits_result) = rev (take (Z.to_nat n) bits_result)) as Hdrop_rev.
  { apply drop_rev_take; auto. }
  
  (* Now we can relate the left and right sides *)
  destruct (rev bits_result) eqn:Hrev.
  - (* Empty list case *)
    (* If rev bits_result is empty, then bits_result must be empty too *)
    assert (bits_result = []) by (apply rev_empty_is_empty; auto).
    subst bits_result.
    rewrite length_nil in Hlen.
    (* This is a contradiction since n+1 > 0 *)
    exfalso. 
    rewrite Z2Nat.inj_add in Hlen; try lia.
  - (* Non-empty list case *)
    (* First, simplify the left-hand side *)
    simpl.
    (* Relate the length of bits_result to n *)
    assert (length bits_result - 1 = Z.to_nat n) as Hlen_minus_1.
    { rewrite Hlen. rewrite Z2Nat.inj_add; try lia. }
    
    (* Simplify the right-hand side *)
    rewrite length_take.
    rewrite Nat.min_l; try lia.
    
    (* Focus on the left-hand side *)
    assert (length bits_result - 1 - 1 = Z.to_nat n - 1) as Hleft_index.
    { rewrite Hlen_minus_1. reflexivity. }
    
    (* Show that the lists being processed are the same *)
    rewrite <- Hdrop_rev.
    
    (* Now we need to handle the accumulator difference *)
    assert (Z.to_nat carry_val * 2 ^ (length bits_result - 1) = 
            Z.to_nat carry_val * 2 ^ Z.to_nat n)%nat as Hacc.
    { 
      f_equal. 
      f_equal.
      assert ((length bits_result - 1)%nat = Z.to_nat (length bits_result - 1)) as Hscope by (apply length_minus_one_nat_z).
      rewrite Hscope.
      rewrite Hlen_minus_1.
      lia.
    }
    
    (* Now we need to relate the two expressions *)
    rewrite Hdrop_rev.
    
    (* We need to show that the recursive functions compute the same value *)
    assert ((fix go (i : nat) (l0 : list Z) {struct l0} : nat :=
         match l0 with
         | [] => Z.to_nat 0
         | b :: bs => (Z.to_nat (b * 2 ^ i) + Z.to_nat (go (i - 1)%nat bs))%nat
         end) (length bits_result - 1 - 1)%nat l =
         (fix go (i : nat) (l0 : list Z) {struct l0} : nat :=
         match l0 with
         | [] => Z.to_nat 0
         | b :: bs => (Z.to_nat (b * 2 ^ i) + Z.to_nat (go (i - 1)%nat bs))%nat
         end) (Z.to_nat n - 1)%nat (rev (take (Z.to_nat n) bits_result))) as Hgo_eq.
    {
      f_equal.
      - apply length_minus_one_equals_n.
        + exact Hlen.
        + exact Hn.
      - exact Hdrop_rev.
    }
    rewrite Hgo_eq.
    rewrite Nat.add_comm.
    f_equal.
    -- apply bits_to_nat_rev_take_eq; auto.
    -- assert ((length bits_result - 1)%nat =  Z.to_nat n) as H1 by (apply length_minus_one_equals_n_simple; auto).
       rewrite H1.
       pose proof rearrange_nat as H2.
       rewrite H2; auto.
    Qed.
    

Lemma partial_sum_complete (i : nat) (carry_val : Z) (bits_result : list Z)
                          (bits_a bits_b : list Z) (n : Z) :
  i ≤ n →
  ¬ i < n →
  length bits_a = Z.to_nat n ->
  length bits_b = Z.to_nat n ->
  length bits_result = Z.to_nat (n + 1) ->
  partial_sum_correct i carry_val bits_result bits_a bits_b →
  n >= 0 ->
  (carry_val = 0 ∨ carry_val = 1) ->
  bits_to_nat (<[Z.to_nat n:=carry_val]> bits_result) = Z.to_nat (bits_to_nat bits_a + bits_to_nat bits_b).
Proof.
  intros Hle Hnlt Hpartial Ha Hb Hresult Hn Hcarry.
  assert (i = Z.to_nat n) as Heq by lia.
  subst i.
  unfold partial_sum_correct in Hresult.
  assert (take (Z.to_nat n) bits_a = bits_a) as Htake_a.
  { apply take_ge. lia. }
  assert (take (Z.to_nat n) bits_b = bits_b) as Htake_b.
  { apply take_ge. lia. }
  rewrite Htake_a in Hresult.
  rewrite Htake_b in Hresult.
  (* We need to relate the bits_to_nat of the updated result to the original expression *)
  assert (bits_to_nat (<[Z.to_nat n:=carry_val]> bits_result) = 
         (bits_to_nat (take (Z.to_nat n) bits_result) + Z.to_nat carry_val * 2 ^ Z.to_nat n)%nat) as Hbits.
  { apply bits_to_nat_insert; auto. }
  rewrite Hbits. symmetry.
  (* We need to convert between nat and Z *)
  rewrite <- (Z2Nat.id (bits_to_nat bits_a + bits_to_nat bits_b)); try lia.
  Qed.

Lemma binary_sum_min_bound (bits_a bits_b : list Z) (i : nat) (y y0 : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i = Some y →
  bits_b !! i = Some y0 →
  min_int i32 ≤ y + y0.
Proof.
  intros Hbinary_a Hbinary_b Hlookup_a Hlookup_b.
  unfold is_binary in Hbinary_a, Hbinary_b.
  apply Forall_lookup with (i:=i) (x:=y) in Hbinary_a; auto.
  apply Forall_lookup with (i:=i) (x:=y0) in Hbinary_b; auto.
  
  (* Since y and y0 are binary digits (0 or 1), their sum is at least 0 *)
  destruct Hbinary_a as [Hy0 | Hy1].
  - destruct Hbinary_b as [Hy00 | Hy01].
    + subst. pose proof (min_int_le_0 i32). lia.
    + subst. pose proof (min_int_le_0 i32). lia.
  - destruct Hbinary_b as [Hy00 | Hy01].
    + subst. pose proof (min_int_le_0 i32). lia.
    + subst. pose proof (min_int_le_0 i32). lia.
Qed.

Lemma binary_sum_with_carry_bound (bits_a bits_b : list Z) (i : nat) (y y0 carry_val : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! i = Some y →
  bits_b !! i = Some y0 →
  (carry_val = 0 ∨ carry_val = 1) →
  y + y0 + carry_val ≤ max_int i32.
Proof.
  intros Hbinary_a Hbinary_b Hlookup_a Hlookup_b Hcarry.
  unfold is_binary in Hbinary_a, Hbinary_b.
  apply Forall_lookup with (i:=i) (x:=y) in Hbinary_a; auto.
  apply Forall_lookup with (i:=i) (x:=y0) in Hbinary_b; auto.
  
  (* Since y, y0, and carry_val are all either 0 or 1, their sum is at most 3 *)
  assert (y + y0 + carry_val ≤ 3) by (
    destruct Hbinary_a, Hbinary_b, Hcarry; subst; lia
  ).
  
  (* And 3 is certainly less than max_int i32 (which is at least 127) *)
  pose proof (max_int_ge_127 i32).
  lia.
Qed.


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
  destruct Hbinary_a as [Hy0 | Hy1]; destruct Hbinary_b as [Hy00 | Hy01]; destruct Hcarry as [Hc0 | Hc1]; subst; lia.
Qed.

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
