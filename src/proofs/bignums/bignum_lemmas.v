From refinedc.typing Require Import typing.
(* TODO remove unused lemmas *)
(* TODO format *)
(* TODO Make names better *)
(* TODO Use vec of bools instead? *)


Definition bits_to_int (bits : list Z) : nat :=
  let fix go i l :=
    match l with
    | [] => 0
    | b :: bs => ((b * 2^i) + (go (i-1) bs))
    end
  in Z.to_nat (go (length bits - 1) (rev bits)).


Definition partial_sum_correct (i : nat) (carry : Z) (bits_result : list Z)
                              (bits_a bits_b : list Z) :=
    (bits_to_int (take i bits_a) + bits_to_int (take i bits_b)) =
    bits_to_int (take i bits_result) + Z.to_nat carry * 2^i.


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
  
  assert (y + y0 <= 2) by (
    destruct Hbinary_a, Hbinary_b; subst; lia
  ).
  
  pose proof (max_int_ge_127 i32).
  lia.
Qed.


Lemma bits_to_int_rev_take_eq (bits_result : list Z) (n : Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  is_binary (take (Z.to_nat n) bits_result) ->
  (fix go (i : Z) (l0 : list Z) {struct l0} : Z :=
     match l0 with
     | [] =>  0
     | b :: bs => ( (b * 2 ^ i) +  (go (i - 1) bs))
     end) ( Z.to_nat n - 1) (rev (take (Z.to_nat n) bits_result))=
   Z.to_nat
    ((fix go (i : Z) (l0 : list Z) {struct l0} : Z :=
        match l0 with
        | [] => 0
        | b :: bs => ((b * 2 ^ i) +  (go (i - 1) bs))
        end) ( Z.to_nat n - 1) (rev (take (Z.to_nat n) bits_result))).
Proof.
  intros.
  remember ((fix go (i : Z) (l0 : list Z) {struct l0} : Z :=
     match l0 with
     | [] =>  0
     | b :: bs => ( (b * 2 ^ i) +  (go (i - 1) bs))
     end) ( Z.to_nat n - 1) (rev (take (Z.to_nat n) bits_result))).
  assert (z >= 0).
  - assert ( forall (n' :nat) (i':Z) (l' :list Z), (is_binary l' ) ->   (n' = Z.to_nat i') -> (length l' = Z.to_nat(i'+1)) -> (fix go (i : Z) (l0 : list Z) {struct l0} : Z :=
       match l0 with
       | [] => 0
       | b :: bs => b * 2 ^ i + go (i - 1) bs
       end) i' l' >=0).
    + intro n'.
      induction n'.
      * intros.
        assert ((length l' = 1%nat) \/ (length l' = 0%nat)).
        {
          lia.
        }
        destruct l'.
        -- lia.
        -- destruct l'.
           ++
              unfold is_binary in H2.
              rewrite Forall_lookup in H2.
              specialize (H2 0%nat z0).
              simpl in H2.
              assert (z0 = 0 ∨ z0 = 1).
              { apply H2. auto. }
              lia.
           ++ exfalso.
              simpl length in H4.
              replace (0+1) with 1 in H4.
              ** replace (Z.to_nat 1) with (S 0) in H4.
                --- simpl in H5. destruct H5; congruence.
                --- lia.
              ** lia.
      * intros.
        specialize (IHn' (i'-1)).
        destruct l'.
        { lia. }
        specialize (IHn' l').
        rewrite Z.ge_le_iff.
        apply Z.add_nonneg_nonneg.
        -- unfold is_binary in H2.
              rewrite Forall_lookup in H2.
              specialize (H2 0%nat z0).
              simpl in H2.
              assert (z0 = 0 ∨ z0 = 1).
              { apply H2. auto. }
              lia.
        -- rewrite <- Z.ge_le_iff.
        apply IHn'.
        ** unfold is_binary in *.
        apply Forall_inv_tail in H2.
        exact H2.
        ** lia.
        ** simpl in H4. lia.
    + specialize (H2 ( Z.to_nat (n - 1)) ( Z.to_nat n - 1) (rev (take (Z.to_nat n) bits_result))).
      rewrite Heqz.
      apply H2.
      * apply Forall_rev. auto.
      * lia.
      * assert ((length (take (Z.to_nat n) bits_result)) = Z.to_nat n) as Hc.
        -- rewrite length_take_le; lia.
        -- rewrite length_rev.
           rewrite Hc.
           lia.
  - lia.
  Qed.

Lemma bits_to_int_take_step (bits : list Z) (i : nat) (x : Z) :
  bits !! i = Some x →
  length bits > i ->
  is_binary (take (i+1) bits) ->
  bits_to_int (take (i + 1) bits) = Z.to_nat ((bits_to_int (take i bits) + x * 2^i)).
Proof.
  intros H H0 Hbin.
  unfold bits_to_int.
           assert (length (take i bits) = i) as Hb.
            {
              apply length_take_le.
              lia.
            }
  assert (take (S i) bits = take i bits ++ [x]).
  - apply take_S_r. auto.
  - assert (Z.to_nat (i + 1) = S i) as Ha by lia.
    rewrite <- Ha in H1.
    assert (take (Z.to_nat (i + 1)) bits = take (i + 1) bits).
    + f_equal. lia.
    + rewrite <- H2.
      rewrite H1.
      assert (rev (take i bits ++ [x]) = x :: rev (take i bits)) as H3.
      --
         pose proof reverse_cons (rev (take i bits)) x.
         unfold reverse in H3.
         rewrite <- rev_alt in H3.
         rewrite <- rev_alt in H3.
         rewrite rev_involutive in H3.
         rewrite <- H3.
         rewrite rev_involutive.
         auto.
      -- rewrite H3.
         assert (length (take i bits ++ [x]) - 1 - 1 = i-1) as H4.
         * rewrite length_app.
           simpl.
           rewrite Hb.
           lia.

         * rewrite H4.
           assert (length (take i bits) - 1 = i - 1) as H5.
           ++ lia.
           ++ rewrite H5.
              remember ((fix go (i0 : Z) (l : list Z) {struct l} : Z :=
           match l with
           | [] => 0
           | b :: bs => b * 2 ^ i0 + go (i0 - 1) bs
           end) (i - 1) (rev (take i bits))).
            assert (length (take i bits ++ [x]) - 1 = i) as H6.
            +++ lia.
            +++ rewrite H6.
                rewrite Z.add_comm.
                f_equal.
                f_equal.
                rewrite Heqz.
                pose proof (bits_to_int_rev_take_eq (take (i+1) bits) (Z.of_nat i)).
                replace (Z.to_nat i) with i in H7 by lia.
                replace (take i (take (i + 1) bits)) with (take i bits) in H7.
                2: {
                  rewrite take_take.
                  f_equal.
                  lia.
                  }
                apply H7.
                *** replace (Z.to_nat (i + 1)) with ((i + 1)%nat) by lia.
                    apply length_take_le.
                    lia.
                *** lia.
                ***
                  replace (take i bits) with (take i (take (i+1) bits)).
                  2: {
                    rewrite take_take.
                    f_equal.
                    lia.
                  }
                  apply Forall_take.
                  auto.
                  Qed.

Lemma rearrange_z (a :Z) (b: Z ) ( i_val: nat) :
  a >= 0  ->
  b >= 0  ->
  (Z.to_nat (a * 2 ^ i_val) +
   Z.to_nat b * 2 ^ (i_val + 1)%nat) =
  ((Z.to_nat a + 2 * Z.to_nat b) * 2 ^ i_val).
Proof.
  intros.
  replace ((2 ^ (i_val + 1)%nat)) with ((2 * 2 ^ i_val)).
  - replace (Z.to_nat (a * 2 ^ i_val)) with (Z.to_nat (Z.to_nat a * 2 ^ i_val)); lia.
  - replace (2 ^ (i_val + 1)%nat) with (2 ^ (i_val + 1)).
    ++ rewrite Z.pow_add_r; lia.
    ++ lia.
  Qed.

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
  length bits_a = Z.to_nat n ->
  length bits_b = Z.to_nat n ->
  is_binary (take i_val current_result) ->
  partial_sum_correct (i_val + 1) ((y + y0 + carry_val) `quot` 2)
    (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result) bits_a bits_b.
Proof.
  intros.
  assert (y0 = 0 ∨ y0 = 1) as Hy0.
  {apply Forall_lookup with (i:=i_val) (x:=y0) in H0; auto. }
  assert (y = 0 ∨ y = 1) as Hy.
  {apply Forall_lookup with (i:=i_val) (x:=y) in H; auto. }
  unfold partial_sum_correct.
  unfold partial_sum_correct in H2.
  rewrite (bits_to_int_take_step bits_a i_val y); auto.
  2: {lia. }
  2: {apply Forall_take. auto. }
  rewrite (bits_to_int_take_step bits_b i_val y0); auto.
  2: {lia. }
  2: {apply Forall_take. auto. }
  rewrite (bits_to_int_take_step (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result) i_val ((y + y0 + carry_val) `rem` 2)).
  - rewrite (Z.add_comm (bits_to_int (take i_val bits_a)) (y * 2 ^ i_val)).
    replace (Z.to_nat (y * 2 ^ i_val + bits_to_int (take i_val bits_a)) +
  Z.to_nat (bits_to_int (take i_val bits_b) + y0 * 2 ^ i_val))
            with
            (y * 2 ^ i_val + bits_to_int (take i_val bits_a) + bits_to_int (take i_val bits_b) + y0 * 2 ^ i_val) by lia.
    rewrite <- (Z.add_assoc (_) (bits_to_int _) (bits_to_int _)).
    rewrite H2.
    assert (take i_val current_result = take i_val (<[i_val:=(y + y0 + carry_val) `rem` 2]> current_result)) as Ha.
    {
      symmetry.
      apply take_insert.
      lia.
    }
    rewrite <- Ha.
    replace (y * 2 ^ i_val +
  (bits_to_int (take i_val current_result) + Z.to_nat carry_val * 2 ^ i_val) +
  y0 * 2 ^ i_val)
             with
(bits_to_int (take i_val current_result) + (y * 2 ^ i_val + Z.to_nat carry_val * 2 ^ i_val +
       y0 * 2 ^ i_val) ) by lia.
    replace
 (Z.to_nat
    (bits_to_int (take i_val current_result) +
     (y + y0 + carry_val) `rem` 2 * 2 ^ i_val) +
  Z.to_nat ((y + y0 + carry_val) `quot` 2) * 2 ^ (i_val + 1)%nat
)    with
(bits_to_int (take i_val current_result) +
 (Z.to_nat ((y + y0 + carry_val) `rem` 2 * 2 ^ i_val) +
  Z.to_nat ((y + y0 + carry_val) `quot` 2) * 2 ^ (i_val + 1)%nat
)).
    * apply Z.add_cancel_l.

      assert ((y + Z.to_nat carry_val  + y0) = (Z.to_nat ((y + y0 + carry_val) `rem` 2 ) + 2 * Z.to_nat ((y + y0 + carry_val) `quot` 2) )).
      + destruct H1; destruct Hy; destruct Hy0; lia.
      + replace ((y * 2 ^ i_val + Z.to_nat carry_val * 2 ^ i_val +
                y0 * 2 ^ i_val)) with ((y + Z.to_nat carry_val +
                y0 )* 2 ^ i_val) by lia.
        pose proof (rearrange_z ((y + y0 + carry_val) `rem` 2) ((y + y0 + carry_val) `quot` 2) i_val) as H12.
        rewrite H12.
        -- rewrite H11. reflexivity.
        -- lia.
        -- lia.
    * remember (bits_to_int (take i_val current_result)).
      remember ((y + y0 + carry_val) `rem` 2 * 2 ^ i_val).
      remember (Z.to_nat ((y + y0 + carry_val) `quot` 2)).
      remember (n1 * 2 ^ (i_val + 1)%nat).
      rewrite Z.add_assoc.
      rewrite Z.add_cancel_r.
      assert (z >= 0) by lia.
      lia.
  - apply list_lookup_insert.
    lia.
  - rewrite length_insert.
    lia.
  - rewrite take_insert_lt.
    * replace current_result with (take i_val current_result ++ drop i_val current_result ) by (apply take_drop).
      remember (take i_val current_result).
      replace i_val with (length l).
      2: {
        rewrite Heql.
        rewrite length_take.
        (* TODO do i need lia? *)
        auto. lia. }

      rewrite take_app_add.
      replace (length l) with ((length l + 0)%nat) by lia.
      rewrite insert_app_r.
      remember (drop (length l + 0) current_result).
      rewrite insert_take_drop.
      + replace (take 0 (take 1 l0)) with ([]: list Z).
        2: {
          rewrite take_take.
          simpl.
          auto.
          }
        replace (drop 1 (take 1 l0)) with ([]: list Z).
        2: {
          unfold take.
          unfold drop.
          destruct l0; auto.
          }
        apply Forall_app.
        split.
        -- auto.
        -- simpl.
           auto.
           remember ((y + y0 + carry_val) `rem` 2).
           assert (z = 0 ∨ z = 1).
           ++ rewrite Heqz.
              lia.
           ++ auto.
      +
        rewrite Heql0.
        rewrite Heql.
        rewrite length_take_le; try lia.
        rewrite length_take_le; try lia.
        rewrite length_drop.
        lia.
    * lia.
    Qed.

Lemma rev_empty_is_empty (l : list Z) :
  rev l = [] -> l = [].
Proof.
  intro H.
  apply rev_inj.
  rewrite H.
  reflexivity.
  Qed.


Lemma rev_insert_first2 (len : nat) (carry_val : Z):
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
(* It may be possible to prove this without strong induction, just using *)
(* rev (rev l) = l *)
Lemma rev_insert_first1 (n : Z) (carry_val : Z) (bits_result : list Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  rev (<[Z.to_nat n:=carry_val]> bits_result) = <[0%nat:=carry_val]> (rev bits_result).
Proof.
  pose proof rev_insert_first2.
  specialize (H (Z.to_nat (n + 1)) carry_val bits_result).
  intros.
  assert (Z.to_nat (Z.to_nat (n + 1) - 1) = Z.to_nat n) as H2 by lia.
  rewrite H2 in H.
  auto.
  Qed.

Lemma length_minus_one_equals_n1 (bits_result : list Z) (n : Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  (length bits_result - 1 - 1) = (Z.to_nat n - 1).
Proof. intros H. rewrite H. lia.
Qed.




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



Lemma bits_to_int_insert (n : Z) (carry_val : Z) (bits_result : list Z) :
  length bits_result = Z.to_nat (n + 1) ->
  n >= 0 ->
  (carry_val = 0 ∨ carry_val = 1) ->
  is_binary (take (Z.to_nat n) bits_result) ->
  bits_to_int (<[Z.to_nat n:=carry_val]> bits_result) =
  Z.to_nat (bits_to_int (take (Z.to_nat n) bits_result) + Z.to_nat carry_val * 2 ^ Z.to_nat n).
Proof.
  intros Hlen Hn Hcarry Hbin.
  unfold bits_to_int.
  rewrite length_insert.

  assert (rev (<[Z.to_nat n:=carry_val]> bits_result) = <[0%nat:=carry_val]> (rev bits_result)) as Hrev_insert.
  { apply rev_insert_first1; auto. }
  rewrite Hrev_insert.

  assert (drop 1 (rev bits_result) = rev (take (Z.to_nat n) bits_result)) as Hdrop_rev.
  { apply drop_rev_take; auto. }

  destruct (rev bits_result) eqn:Hrev.
  - assert (bits_result = []) by (apply rev_empty_is_empty; auto).
    subst bits_result.
    rewrite length_nil in Hlen.
    exfalso.
    rewrite Z2Nat.inj_add in Hlen; try lia.
  - simpl.
    assert (length bits_result - 1 = Z.to_nat n) as Hlen_minus_1.
    { rewrite Hlen. rewrite Z2Nat.inj_add; try lia. }

    rewrite length_take.
    rewrite Nat.min_l; try lia.

    assert (length bits_result - 1 - 1 = Z.to_nat n - 1) as Hleft_index.
    { rewrite Hlen_minus_1. reflexivity. }

    rewrite <- Hdrop_rev.

    rewrite Hdrop_rev.

    assert ((fix go (i : Z) (l0 : list Z) {struct l0} : Z :=
         match l0 with
         | [] => 0
         | b :: bs => ((b * 2 ^ i) + (go (i - 1) bs))
         end) (length bits_result - 1 - 1) l =
         (fix go (i : Z) (l0 : list Z) {struct l0} : Z :=
         match l0 with
         | [] => 0
         | b :: bs => ((b * 2 ^ i) + (go (i - 1) bs))
         end) (Z.to_nat n - 1) (rev (take (Z.to_nat n) bits_result))) as Hgo_eq.
    {
      f_equal.
      - apply length_minus_one_equals_n1.
        + exact Hlen.
        + exact Hn.
      - exact Hdrop_rev.
    }
    rewrite Hgo_eq.
    rewrite Z.add_comm.
    f_equal.
    f_equal.
    -- apply bits_to_int_rev_take_eq; auto.
    -- rewrite Hlen.
       f_equal.
       ++ lia.
       ++ f_equal. lia.
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
  (is_binary (take i bits_result)) ->
  bits_to_int (<[Z.to_nat n:=carry_val]> bits_result) = Z.to_nat (bits_to_int bits_a + bits_to_int bits_b).
Proof.
  intros Hle Hnlt Hpartial Ha Hb Hresult Hn Hcarry Hbin.
  assert (i = Z.to_nat n) as Heq by lia.
  subst i.
  unfold partial_sum_correct in Hresult.
  assert (take (Z.to_nat n) bits_a = bits_a) as Htake_a.
  { apply take_ge. lia. }
  assert (take (Z.to_nat n) bits_b = bits_b) as Htake_b.
  { apply take_ge. lia. }
  rewrite Htake_a in Hresult.
  rewrite Htake_b in Hresult.
  assert (bits_to_int (<[Z.to_nat n:=carry_val]> bits_result) =
         Z.to_nat (bits_to_int (take (Z.to_nat n) bits_result) + Z.to_nat carry_val * 2 ^ Z.to_nat n)) as Hbits.
  { apply bits_to_int_insert; auto.

  }
  rewrite Hbits. symmetry.
  rewrite Hresult.
  reflexivity.
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
  
  assert (y + y0 + carry_val ≤ 3) by (
    destruct Hbinary_a, Hbinary_b, Hcarry; subst; lia
  ).
  
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
  - destruct (decide (j = i_val)) as [Heq|Hneq].
    + subst j.
      rewrite lookup_take in Hj; try lia.
      rewrite list_lookup_insert in Hj; try lia.
    -- injection Hj as Hj; subst x.
      assert (0 <= (y + y0 + carry_val) `rem` 2 < 2) as Hrem.
      { 
        apply Z.rem_bound_pos.
        - apply binary_sum_non_negative with (bits_a:=bits_a) (bits_b:=bits_b) (i:=i_val); auto.
        - lia.
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
    + rewrite lookup_take in Hj; try lia.
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
  * subst i.
    rewrite list_lookup_insert in Hi.
    + injection Hi as Hi; subst x; exact Hcarry.
    + rewrite Hlength.
      rewrite Z2Nat.inj_add; try lia.
  * rewrite list_lookup_insert_ne in Hi; auto.
    destruct (decide (i < i_val)%nat) as [Hlt|Hnlt'].
    + unfold is_binary in Hbinary.
      assert (take i_val current_result !! i = Some x) as Htake.
      { rewrite lookup_take; auto. }
      apply (Forall_lookup_1 _ _ _ _ Hbinary Htake).
    + exfalso.
      assert (i < Z.to_nat n)%nat.
      { apply (lookup_lt_Some current_result i x) in Hi.
        rewrite Hlength in Hi.
        destruct (decide (i < Z.to_nat n)%nat); auto.
        assert (i = Z.to_nat n) by lia. contradiction. }
      assert (i_val ≤ i)%nat by lia.
      apply Hnlt. lia.
  Qed.
