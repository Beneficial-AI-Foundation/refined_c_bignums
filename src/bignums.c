//@rc::import bignum_lemmas from refinedc.project.workspace.src.bignums
// Bignum addition where numbers are represented as arrays of 0s and 1s (LSB first)
// E.g., 5 = [1,0,1,0,...] represents 1*2^0 + 0*2^1 + 1*2^2 = 1 + 4 = 5

/* Helper: convert a list of bits to the natural number it represents */
// Definition bits_to_nat (bits : list Z) : nat := 
//   fold_left (fun acc b => 2 * acc + Z.to_nat b) (rev bits) 0.

/* Helper: check if all elements are 0 or 1 */
// Definition is_binary (bits : list Z) := Forall (fun b => b = 0 ∨ b = 1) bits.

/* Add two bignums with carry */
[[rc::parameters("a_loc : loc", "b_loc : loc", "result_loc : loc", 
                 "bits_a : {list Z}", "bits_b : {list Z}", "n : Z", "initial_result : {list Z}")]]
[[rc::args("a_loc @ &own<array<i32, {bits_a `at_type` (int i32)}>>",
           "b_loc @ &own<array<i32, {bits_b `at_type` (int i32)}>>", 
           "result_loc @ &own<array<i32, {initial_result `at_type` (int i32)}>>",
           "n @ int<i32>")]]
[[rc::requires("{length initial_result = Z.to_nat (n + 1)}")]]
[[rc::requires("{length bits_a = Z.to_nat n}", "{length bits_b = Z.to_nat n}",
               "{is_binary bits_a}", "{is_binary bits_b}")]]
[[rc::requires("{n > 0}", "{n < max_int i32}")]]
[[rc::returns("void")]]
[[rc::ensures("own a_loc : array<i32, {bits_a `at_type` (int i32)}>")]]
[[rc::ensures("own b_loc : array<i32, {bits_b `at_type` (int i32)}>")]]
[[rc::exists("final_result : {list Z}")]]
[[rc::ensures("own result_loc : array<i32, {final_result `at_type` (int i32)}>")]]
[[rc::ensures("{length final_result = Z.to_nat (n + 1)}")]]
[[rc::ensures("{is_binary final_result}")]]
[[rc::ensures("{bits_to_nat final_result = Z.to_nat ((Z.of_nat (bits_to_nat bits_a) + Z.of_nat (bits_to_nat bits_b)) )}")]]
[[rc::lemmas("binary_sum_within_i32_bounds",
             "partial_sum_complete", "binary_sum_min_bound", "binary_sum_with_carry_bound",
             "binary_add_quot", "binary_rem_is_binary", "initial_partial_sum_correct",
             "binary_update_preserves_binary", "carry_update_preserves_binary",
             "partial_sum_step_exact")]]
[[rc::tactics("all: try solve [eauto using binary_sum_within_i32_bounds | eauto using binary_sum_with_carry_bound | eauto using binary_add_quot].")]]
[[rc::tactics("all: try solve [eauto using binary_sum_min_bound].")]]
[[rc::tactics("all: try solve [eauto using initial_partial_sum_correct].")]]
[[rc::tactics("all: try solve [eapply partial_sum_complete with (i:=i_val) (carry_val:=carry_val) (bits_result:=current_result) (bits_a:=bits_a) (bits_b:=bits_b) (n:=n); eauto].")]]
[[rc::tactics("all: try solve [eapply binary_update_preserves_binary with (bits_a:=bits_a) (bits_b:=bits_b) (y:=y) (y0:=y0) (carry_val:=carry_val); eauto].")]]
[[rc::tactics("all: try solve [eapply carry_update_preserves_binary with (i_val:=i_val) (carry_val:=carry_val); eauto].")]]
void bignum_add(int* a, int* b, int* result, int n) {
    int carry = 0;
    
    [[rc::exists("i_val : nat", "carry_val : Z", "current_result : {list Z}")]]
    [[rc::inv_vars("i : i_val @ int<i32>", "carry : carry_val @ int<i32>", 
                   "result : result_loc @ &own<array<i32, {current_result `at_type` (int i32)}>>")]]
    [[rc::constraints("{0 <= i_val}", "{i_val <= Z.to_nat n}", "{carry_val = 0 ∨ carry_val = 1}")]]
    [[rc::constraints("{length current_result = Z.to_nat (n + 1)}")]]
    [[rc::constraints("{is_binary (firstn i_val current_result)}")]]
    [[rc::constraints("{partial_sum_correct i_val carry_val current_result bits_a bits_b}")]]
    for (int i = 0; i < n; i++) {
        int bit_sum = a[i] + b[i] + carry;
        result[i] = bit_sum % 2;
        carry = bit_sum / 2;
    }
    
    result[n] = carry;
}
