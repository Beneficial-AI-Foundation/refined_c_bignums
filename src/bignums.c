//@rc::import bignum_lemmas from refinedc.project.workspace.src.bignums
// Bignum addition where numbers are represented as arrays of 0s and 1s (LSB first)
// E.g., 5 = [1,0,1,0,...] represents 1*2^0 + 0*2^1 + 1*2^2 = 1 + 4 = 5

/* Helper: convert a list of bits to the natural number it represents */
// Definition bits_to_nat (bits : list Z) : nat := 
//   fold_left (fun acc b => 2 * acc + Z.to_nat b) (rev bits) 0.

/* Helper: check if all elements are 0 or 1 */
// Definition is_binary (bits : list Z) := Forall (fun b => b = 0 ∨ b = 1) bits.

/* Add two bignums with carry */
[[rc::parameters("a : loc", "b : loc", "result : loc", 
                 "bits_a : {list Z}", "bits_b : {list Z}", "n : Z", "bits_result : {list Z}")]]
[[rc::args("a @ &own<array<i32, {bits_a `at_type` (int i32)}>>",
           "b @ &own<array<i32, {bits_b `at_type` (int i32)}>>", 
           "result @ &own<array<i32, {bits_result `at_type` (int i32)}>>",
           "n @ int<i32>")]]
[[rc::requires("{bits_result = replicate (Z.to_nat (n + 1)) (0:Z)}")]]
[[rc::requires("{length bits_a = Z.to_nat n}", "{length bits_b = Z.to_nat n}",
               "{is_binary bits_a}", "{is_binary bits_b}")]]
[[rc::requires("{n > 0}", "{n < max_int i32}")]]
[[rc::returns("void")]]
[[rc::ensures("own a : array<i32, {bits_a `at_type` (int i32)}>")]]
[[rc::ensures("own b : array<i32, {bits_b `at_type` (int i32)}>")]]
[[rc::ensures("own result : array<i32, {bits_result `at_type` (int i32)}>")]]
[[rc::ensures("{length bits_result = Z.to_nat (n + 1)}")]]
[[rc::ensures("{is_binary bits_result}")]]
[[rc::ensures("{bits_to_nat bits_result = Z.to_nat ((Z.of_nat (bits_to_nat bits_a) + Z.of_nat (bits_to_nat bits_b)) )}")]]
[[rc::lemmas("binary_add_step", "binary_add_carry_bound", "bits_to_nat_app", "binary_sum_within_i32_bounds", "partial_sum_complete", "binary_sum_min_bound")]]
[[rc::tactics("all: try by apply (binary_sum_within_i32_bounds bits_a bits_b i y y0 H1 H2 H15 H17).")]]
[[rc::tactics("all: try by apply (binary_sum_min_bound bits_a bits_b i y y0 H1 H2 H15 H17).")]]
[[rc::tactics("all: try by apply (partial_sum_complete i carry_val bits_result bits_a bits_b n H6 H14 H9).")]]
void bignum_add(int* a, int* b, int* result, int n) {
    int carry = 0;
    
    [[rc::exists("i : nat", "carry_val : Z")]]
    [[rc::inv_vars("i : i @ int<i32>", "carry : carry_val @ int<i32>")]]
    [[rc::constraints("{0 <= i}", "{i <= Z.to_nat n}", "{carry_val = 0 ∨ carry_val = 1}")]]
    [[rc::constraints("{is_binary bits_result}")]]
    [[rc::constraints("{partial_sum_correct i carry_val bits_result bits_a bits_b}")]]
    for (int i = 0; i < n; i++) {
        int bit_sum = a[i] + b[i] + carry;
        result[i] = bit_sum % 2;
        carry = bit_sum / 2;
    }
    
    result[n] = carry;
}
