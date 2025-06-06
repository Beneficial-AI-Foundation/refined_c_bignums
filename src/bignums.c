// Bignum addition where numbers are represented as arrays of 0s and 1s (LSB first)
// E.g., 5 = [1,0,1,0,...] represents 1*2^0 + 0*2^1 + 1*2^2 = 1 + 4 = 5

/* Helper: convert a list of bits to the natural number it represents */
// Definition bits_to_nat (bits : list Z) : nat := 
//   fold_left (fun acc b => 2 * acc + Z.to_nat b) (rev bits) 0.

/* Helper: check if all elements are 0 or 1 */
// Definition is_binary (bits : list Z) := Forall (fun b => b = 0 ∨ b = 1) bits.

/* Add two bignums with carry */
[[rc::parameters("a : loc", "b : loc", "result : loc", 
                 "bits_a : {list Z}", "bits_b : {list Z}", "n : nat")]]
[[rc::args("a @ &own<array<i32, {bits_a `at_type` (int i32)}>>",
           "b @ &own<array<i32, {bits_b `at_type` (int i32)}>>", 
           "result @ &own<array<i32, {replicate (n + 1) (0:Z) `at_type` (int i32)}>>",
           "n @ int<i32>")]]
[[rc::requires("{length bits_a = n}", "{length bits_b = n}", 
               "{is_binary bits_a}", "{is_binary bits_b}")]]
[[rc::requires("{n > 0}", "{n < max_int i32}")]]
[[rc::exists("bits_result : {list Z}")]]
[[rc::returns("unit")]]
[[rc::ensures("own a : array<i32, {bits_a `at_type` (int i32)}>")]]
[[rc::ensures("own b : array<i32, {bits_b `at_type` (int i32)}>")]]
[[rc::ensures("own result : array<i32, {bits_result `at_type` (int i32)}>")]]
[[rc::ensures("{length bits_result = n + 1}")]]
[[rc::ensures("{is_binary bits_result}")]]
[[rc::ensures("{bits_to_nat bits_result = (bits_to_nat bits_a + bits_to_nat bits_b) mod (2^(n+1))}")]]
[[rc::lemmas("binary_add_step", "binary_add_carry_bound", "bits_to_nat_app")]]
void bignum_add(int* a, int* b, int* result, int n) {
    int carry = 0;
    
    [[rc::exists("i : nat", "carry_val : Z", "partial_result : {list Z}")]]
    [[rc::inv_vars("i : i @ int<i32>", "carry : carry_val @ int<i32>")]]
    [[rc::constraints("{0 <= i}", "{i <= n}", "{carry_val = 0 ∨ carry_val = 1}")]]
    [[rc::constraints("{length partial_result = i}")]]
    [[rc::constraints("{is_binary partial_result}")]]
    [[rc::constraints("{partial_sum_correct i carry_val partial_result bits_a bits_b}")]]
    for (int i = 0; i < n; i++) {
        int bit_sum = a[i] + b[i] + carry;
        result[i] = bit_sum % 2;
        carry = bit_sum / 2;
    }
    
    result[n] = carry;
}

/* Check if bignum is zero */
[[rc::parameters("a : loc", "bits : {list Z}", "n : nat")]]
[[rc::args("a @ &own<array<i32, {bits `at_type` (int i32)}>>", "n @ int<i32>")]]
[[rc::requires("{length bits = n}", "{is_binary bits}", "{n > 0}")]]
[[rc::returns("is_zero @ int<i32>")]]
[[rc::ensures("own a : array<i32, {bits `at_type` (int i32)}>")]]
[[rc::ensures("{(is_zero = 1) ↔ (bits_to_nat bits = 0)}")]]
[[rc::lemmas("bits_to_nat_all_zero")]]
int bignum_is_zero(int* a, int n) {
    [[rc::exists("i : nat")]]
    [[rc::inv_vars("i : i @ int<i32>")]]
    [[rc::constraints("{0 <= i}", "{i <= n}")]]
    [[rc::constraints("{all_zero_prefix i bits}")]]
    for (int i = 0; i < n; i++) {
        if (a[i] != 0) {
            return 0;
        }
    }
    return 1;
}

/* Compare two bignums */
[[rc::parameters("a : loc", "b : loc", "bits_a : {list Z}", "bits_b : {list Z}", "n : nat")]]
[[rc::args("a @ &own<array<i32, {bits_a `at_type` (int i32)}>>",
           "b @ &own<array<i32, {bits_b `at_type` (int i32)}>>", 
           "n @ int<i32>")]]
[[rc::requires("{length bits_a = n}", "{length bits_b = n}", 
               "{is_binary bits_a}", "{is_binary bits_b}", "{n > 0}")]]
[[rc::returns("cmp @ int<i32>")]]
[[rc::ensures("own a : array<i32, {bits_a `at_type` (int i32)}>")]]
[[rc::ensures("own b : array<i32, {bits_b `at_type` (int i32)}>")]]
[[rc::ensures("{cmp = -1 ↔ bits_to_nat bits_a < bits_to_nat bits_b}")]]
[[rc::ensures("{cmp = 0 ↔ bits_to_nat bits_a = bits_to_nat bits_b}")]]
[[rc::ensures("{cmp = 1 ↔ bits_to_nat bits_a > bits_to_nat bits_b}")]]
[[rc::lemmas("bignum_compare_from_msb", "bits_to_nat_unique")]]
int bignum_compare(int* a, int* b, int n) {
    // Compare from MSB to LSB
    [[rc::exists("i : nat")]]
    [[rc::inv_vars("i : i @ int<i32>")]]  
    [[rc::constraints("{0 <= i}", "{i <= n}")]]
    [[rc::constraints("{equal_suffix i n bits_a bits_b}")]]
    for (int i = n - 1; i >= 0; i--) {
        if (a[i] > b[i]) return 1;
        if (a[i] < b[i]) return -1;
    }
    return 0;
}
