#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

//@rc::inlined
//@Global Instance simpl_both_20_mult_5 n: SimplBoth (20 = n * 5) (n = 4).
//@Proof. split; lia. Qed.
//@rc::end

[[rc::exists("n : Z")]]
[[rc::returns("{n * 5} @ int<i32>")]]
int return_multiple_of_5() {
  return 20;
}

/**
  For some examples of simplification rules see [theories/lithium/simpl_instances.v].
 */
