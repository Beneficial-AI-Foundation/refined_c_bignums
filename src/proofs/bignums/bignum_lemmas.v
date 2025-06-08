From refinedc.typing Require Import typing.


Open Scope nat_scope.
(* Convert a list of bits (LSB first) to a natural number *)
Definition bits_to_nat (bits : list Z) : nat :=
  fold_right (fun b acc => Z.to_nat b + 2 * acc) 0 (rev bits).


(* Partial sum correctness for the first i digits *)
Definition partial_sum_correct (i : nat) (carry : Z) (bits_result : list Z)
                              (bits_a bits_b : list Z) :=
  ∃ (sum : nat),
    sum = (bits_to_nat (take i bits_a) + bits_to_nat (take i bits_b)) ∧
    bits_to_nat (take i bits_result) + Z.to_nat carry * 2^i = sum.

Lemma bits_to_nat_app (bits1 bits2 : list Z) :
  bits_to_nat (bits1 ++ bits2) =
  bits_to_nat bits1 + bits_to_nat bits2 * 2^(length bits1).
Proof. Admitted.

Close Scope nat_scope.

(* Check if all elements are binary (0 or 1) *)
Definition is_binary (bits : list Z) := 
  Forall (fun b => b = 0 ∨ b = 1) bits.




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

Lemma binary_sum_within_i32_bounds (bits_a bits_b : list Z) (partial_result : list Z) (y y0 : Z) :
  is_binary bits_a →
  is_binary bits_b →
  bits_a !! length partial_result = Some y →
  bits_b !! length partial_result = Some y0 →
  y + y0 <= max_int i32.
Proof. Admitted.

(* New lemma for the final step *)
Lemma partial_sum_complete (i : nat) (carry_val : Z) (bits_result : list Z) 
                          (bits_a bits_b : list Z) (n : Z) :
  i ≤ n →
  ¬ i < n →
  partial_sum_correct i carry_val bits_result bits_a bits_b →
  bits_to_nat bits_result = Z.to_nat (bits_to_nat bits_a + bits_to_nat bits_b).
Proof. Admitted.
