relation fib(int n, int f) == 
  (n = 0 & f = 1 | 
   n = 1 & f = 1 | 
   n > 1 & exists(f1,f2 : fib(n-1,f1) & fib(n-2,f2) & f = f1 + f2)).

  //checkentail fib(n,f1) & fib(n,f2) |- f1 = f2.

  //checkentail fib(0,f1) & fib(0,f2) |- f1 = f2.

  //checkentail forall(f1,f2,m : m >= n | !(fib(m,f1)) | !(fib(m,f2)) | f1 = f2)  & fib(n,f1) & fib(n,f2) |- f1 = f2.

relation fact(int n, int f) == 
  (n = 0 & f = 1 | 
   n > 0 & exists(f1 : fact(n-1,f1) & f = n * f1)).

  //checkentail fib(n,f) & fact(n,g) |- f <= g.

  //checkentail fib(0,f) & fact(0,g) |- f <= g.

  //checkentail fib(1,f) & fact(1,g) |- f <= g.

  //checkentail n > 1 & fib(n-1,f1) & fib(n-2,f2) & fact(n-1,g1) & fact(n-2,g2) & f1 <= g1 & f2 <= g2 & fib(n,f) & fact(n,g) |- f = f1 + f2 & g = g1 * n.
// f <= g.

checkentail n > 1 & f = f1 + f2 & 0 <= f1 <= g1 & 0 <= f2 <= g2 & g = g1 * n & g1 = (n-1) * g2 |- f <= g.
