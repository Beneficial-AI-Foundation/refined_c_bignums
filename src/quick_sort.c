//@rc::import quick_sort_lemmas from refinedc.examples.quick_sort

#define LOOP_INVS \
  [[rc::exists("i : nat", "j : nat", "key : Z", "ys : {list Z}")]] \
  [[rc::inv_vars("i : i @ int<i32>", "j : j @ int<i32>", "key : key @ int<i32>", \
                  "arr : a @ &own<array<i32, {ys `at_type` (int i32)}>>")]] \
  [[rc::constraints("{lo <= i}", "{i <= j}", "{j <= hi}", "{length ys = length es}")]] \
  [[rc::constraints("{unchanged lo hi ys es}")]] \
  [[rc::constraints("{partitioned lo i j hi key ys}")]] \

/* Helper function: split `arr[lo..hi]` into two parts: <= pivot and >= pivot */
[[rc::parameters("a : loc", "es : {list Z}", "lo : nat", "hi : nat")]]
[[rc::args("a @ &own<array<i32, {es `at_type` (int i32)}>>", "lo @ int<i32>", "hi @ int<i32>")]]
[[rc::requires("{es <> []}", "{lo < hi}", "{hi < length es}")]]
[[rc::exists("index : nat", "pivot : Z", "xs : {list Z}")]]
[[rc::returns("index @ int<i32>")]]
[[rc::ensures("{lo <= index}", "{index <= hi}")]]
[[rc::ensures("own a : array<i32, {xs `at_type` (int i32)}>")]]
[[rc::ensures("{unchanged lo hi xs es}")]]
[[rc::ensures("{Permutation xs es}")]]
[[rc::ensures("{xs !! index = Some pivot}")]]
[[rc::ensures("{partitioned lo index index hi pivot xs}")]]
[[rc::tactics("all: try simpl_insert; try by solve_goal.")]]
[[rc::tactics("all: try by solve_unchanged.")]]
[[rc::lemmas("perm_insert_swap")]]
[[rc::lemmas("range_forall_empty")]]
[[rc::tactics("all: try by apply: range_forall_extend; eauto; econstructor; solve_goal.")]]
[[rc::tactics("all: try by apply: range_forall_insert; rewrite /elem_of; solve_goal.")]]
[[rc::tactics("all: try by apply: range_forall_insert; (have ? : i = j by solve_goal); rewrite /elem_of; solve_goal.")]]
int partition(int* arr, int lo, int hi)
{
  int i = lo;
  int j = hi;
  int key = arr[i];
  
  LOOP_INVS
  [[rc::constraints("{Permutation (<[i:=key]> ys) es}")]]
  while (i < j)
  {
    LOOP_INVS
    [[rc::constraints("{Permutation (<[i:=key]> ys) es}")]]
    while (i < j && arr[j] >= key)
    {
        --j;
    }
    arr[i] = arr[j];
    
    LOOP_INVS
    [[rc::constraints("{Permutation (<[j:=key]> ys) es}")]]
    while (i < j && arr[i] <= key)
    {
        ++i;
    }
    arr[j] = arr[i];
  }

  arr[i] = key;
  return i;
}

/* Quick sort: sorting `arr[lo..hi]` */
[[rc::parameters("a : loc", "es : {list Z}", "lo : Z", "hi : Z")]]
[[rc::args("a @ &own<array<i32, {es `at_type` (int i32)}>>", "lo @ int<i32>", "hi @ int<i32>")]]
[[rc::requires("{lo >= 0}", "{hi < length es}", "{length es <= max_int i32}")]]
[[rc::exists("xs : {list Z}")]]
[[rc::ensures("own a : array<i32, {xs `at_type` (int i32)}>")]]
[[rc::ensures("{unchanged lo hi xs es}")]]
[[rc::ensures("{Permutation xs es}")]]
[[rc::ensures("{sorted lo hi xs}")]]
[[rc::tactics("all: try by solve_unchanged.")]]
[[rc::tactics("all: try by solve_length_by_perm.")]]
[[rc::tactics("all: try by solve_perm_by_trans.")]]
[[rc::lemmas("sorted_nil", "sorted_qsort")]]
void qsort(int* arr, int lo, int hi)
{
  if (lo < hi)
  {
      int k = partition(arr, lo, hi);
      qsort(arr, lo, k - 1);
      qsort(arr, k + 1, hi);
  }
}
