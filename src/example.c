#include <assert.h>

[[rc::parameters("nx : nat", "ny : nat", "nz : nat")]]
[[rc::args("nx @ int<u32>", "ny @ int<u32>", "nz @ int<u32>")]]
[[rc::requires("{nx + ny ≤ max_int u32}", "{(nx + ny) + nz ≤ max_int u32}")]]
[[rc::returns("{nx + ny + nz} @ int<u32>")]]
unsigned int add3(unsigned int x, unsigned int y, unsigned int z){
  unsigned int r = x + y;
  return r + z;
}

[[rc::returns("{0} @ int<i32>")]]
int main(){
  unsigned int a;

  a = add3(1, 2, 3);
  assert(a == 6u);

  a = add3(a, a, a);
  assert(a == 18u);

  return 0;
}

