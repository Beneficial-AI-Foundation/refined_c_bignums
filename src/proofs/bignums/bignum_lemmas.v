From refinedc.typing Require Import typing.


Open Scope nat_scope.
(* Convert a list of bits (LSB first) to a natural number *)
Definition bits_to_nat (bits : list Z) : nat :=
  fold_right (fun b acc => Z.to_nat b + 2 * acc) 0 (rev bits).


(* Partial sum correctness for the first i digits *)
Definition partial_sum_correct (i : nat) (carry : Z) (partial : list Z)
                              (bits_a bits_b : list Z) :=
  ∃ (sum : nat),
    sum = (bits_to_nat (take i bits_a) + bits_to_nat (take i bits_b)) ∧
    bits_to_nat partial + Z.to_nat carry * 2^i = sum.

Close Scope nat_scope.

(* Check if all elements are binary (0 or 1) *)
Definition is_binary (bits : list Z) := 
  Forall (fun b => b = 0 ∨ b = 1) bits.


(* All zeros up to position i *)
Definition all_zero_prefix (i : nat) (bits : list Z) :=
  ∀ j : nat , j < i → bits !! j = Some 0.

(* Equal from position i to n *)  
Definition equal_suffix (i n : nat) (bits_a bits_b : list Z) :=
  ∀ j : nat , i ≤ j < n → bits_a !! j = bits_b !! j.

(* Key lemmas (statements only) *)

Lemma binary_add_step (a b carry : Z) :
  (a = 0 ∨ a = 1) →
  (b = 0 ∨ b = 1) →
  (carry = 0 ∨ carry = 1) →
  let sum := a + b + carry in
  (sum mod 2 = 0 ∨ sum mod 2 = 1) ∧ (sum `div` 2 = 0 ∨ sum `div` 2 = 1).
Proof. Admitted.

Lemma binary_add_carry_bound (bits_a bits_b : list Z) (i : nat) :
  is_binary bits_a →
  is_binary bits_b →
  bits_to_nat (take i bits_a) + bits_to_nat (take i bits_b) < 2^(i+1).
Proof. Admitted.

Lemma bits_to_nat_app (bits1 bits2 : list Z) :
  bits_to_nat (bits1 ++ bits2) = 
  bits_to_nat bits1 + bits_to_nat bits2 * 2^(length bits1).
Proof. Admitted.

Lemma bits_to_nat_all_zero (bits : list Z) :
  is_binary bits →
  (∀ i, bits !! i = Some 0) ↔ bits_to_nat bits = 0.
Proof. Admitted.

Lemma bignum_compare_from_msb (bits_a bits_b : list Z) :
  is_binary bits_a →
  is_binary bits_b →
  length bits_a = length bits_b →
  ∀ i, bits_a !! i = bits_b !! i ∨
       (bits_a !! i = Some 1 ∧ bits_b !! i = Some 0 ∧ 
        bits_to_nat bits_a > bits_to_nat bits_b) ∨
       (bits_a !! i = Some 0 ∧ bits_b !! i = Some 1 ∧ 
        bits_to_nat bits_a < bits_to_nat bits_b).
Proof. Admitted.

Lemma bits_to_nat_unique (bits_a bits_b : list Z) :
  is_binary bits_a →
  is_binary bits_b →
  length bits_a = length bits_b →
  bits_to_nat bits_a = bits_to_nat bits_b →
  bits_a = bits_b.
Proof. Admitted.

Lemma partial_sum_extend (i : nat) (carry : Z) (partial : list Z) 
                        (bits_a bits_b : list Z) (new_bit : Z) :
  partial_sum_correct i carry partial bits_a bits_b →
  bits_a !! i = Some (Z.of_nat (Z.to_nat new_bit mod 2)) →
  bits_b !! i = Some (Z.of_nat (Z.to_nat new_bit mod 2)) →
  let sum := new_bit + carry in
  partial_sum_correct (i+1) (sum `div` 2) (partial ++ [sum mod 2]) bits_a bits_b.
Proof. Admitted.
