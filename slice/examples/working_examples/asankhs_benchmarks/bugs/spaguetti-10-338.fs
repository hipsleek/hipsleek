tl;

ex338(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) [
x6 != x8 * x6 != x9 *
x3 != x6 * x3 != x4 * x3 != x10 * x3 != x5 *
x2 != x9 * x8 != x10 * x4 != x6 * x1 != x7 * x1 != x2 * x1 != x5 * x5 != x9 *
lseg(x6, x7) *
lseg(x7, x6) *
lseg(x7, x4) *
lseg(x7, x3) *
lseg(x8, x1) *
lseg(x4, x7) *
lseg(x10, x7) *
lseg(x5, x9)] { } [ x1 != x1 ]
