#include <stdlib.h>
/* Return non-zero if xp,xsize and yp,ysize overlap.
   If xp+xsize<=yp there's no overlap, or if yp+ysize<=xp there's no
   overlap.  If both these are false, there's an overlap. */
#define MPN_OVERLAP_P(xp, xsize, yp, ysize)				\
  ((xp) + (xsize) > (yp) && (yp) + (ysize) > (xp))
/* Return non-zero if dst,dsize and src,ssize are either identical or
   overlapping in a way suitable for an incrementing/decrementing algorithm.
   Return zero if they're partially overlapping in an unsuitable fashion. */
#define MPN_SAME_OR_INCR2_P(dst, dsize, src, ssize)			\
  ((dst) <= (src) || ! MPN_OVERLAP_P (dst, dsize, src, ssize))
#define MPN_SAME_OR_INCR_P(dst, src, size)				\
  MPN_SAME_OR_INCR2_P(dst, size, src, size)

[[rc::parameters("n : nat")]]
[[rc::parameters("rp : loc")]]
[[rc::parameters("rp_elts : {list Z}")]]
[[rc::parameters("up : loc")]]
[[rc::parameters("up_elts : {list Z}")]]
[[rc::parameters("vp : loc")]]
[[rc::parameters("vp_elts : {list Z}")]]
[[rc::args("rp @ &own<array<u32, {rp_elts `at_type` (int u32)}>>",
           "up @ &own<array<u32, {up_elts `at_type` (int u32)}>>",
           "vp @ &own<array<u32, {vp_elts `at_type` (int u32)}>>",
           "n @ int<u32>")]]
[[rc::returns("int<u32>")]]
//[[rc::ensures("own rp : array<u32, {replicate n (int u32)}>",
//             "own up : array<u32, {replicate n (int u32)}}>",
//              "own vp : array<u32, {replicate n (int u32)}}>")]]
unsigned int
mpn_add_n (unsigned int *rp, unsigned int *up, unsigned int *vp, unsigned int n)
{
  unsigned int ul, vl, sl, rl, cy, cy1, cy2;

  //ASSERT (n >= 1);
  //ASSERT (MPN_SAME_OR_INCR_P (rp, up, n));
  //ASSERT (MPN_SAME_OR_INCR_P (rp, vp, n));

  cy = 0;
//  do
//    {
//      ul = *up;
//      up++;
//      vl = *vp;
//      vp++;
//      sl = ul + vl;
//      cy1 = sl < ul;
//      rl = sl + cy;
//      cy2 = rl < sl;
//      cy = cy1 | cy2;
//      *rp = rl;
//      rp++;
//      --n;
//    }
//  while (n != 0);

  return cy;
}
