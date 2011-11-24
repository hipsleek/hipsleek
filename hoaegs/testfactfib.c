relation fib(int n, int f)./* ==
  (n = 0 & f = 1 | 
   n = 1 & f = 1 | 
   n > 1 & exists(f1,f2 : fib(n-1,f1) & fib(n-2,f2) & f = f1 + f2) & forall(f3,f4 : !(fib(n-1,f3)) | !(fib(n-2,f4)) | f = f3 + f4)).*/

axiom true ==> fib(0,1) & fib(1,1).

axiom n > 1 & fib(n-1,f1) & fib(n-2,f2) ==> fib(n,f1+f2).

axiom fib(n,f) & n = 0 ==> f = 1.

axiom fib(n,f) & n = 1 ==> f = 1.

axiom fib(n,f) & n > 1 ==> forall(f1,f2 : !(fib(n-1,f1)) | !(fib(n-2,f2)) | f = f1 + f2).

relation fact(int n, int f)./* == 
  (n = 0 & f = 1 | 
   n > 0 & exists(f1 : fact(n-1,f1) & f = n * f1) & forall(f2 : !(fact(n-1,f2)) | f = n * f2)).*/

axiom true ==> fact(0,1).

axiom n > 0 & fact(n-1,f1) ==> fact(n,n*f1).

axiom fact(n,f) & n = 0 ==> f = 1.

axiom fact(n,f) & n > 0 ==> forall(f1 : !(fact(n-1,f1)) | f = f1 * n).

// Theorem: fibonacci is a function

// 1) fibonacci is defined everywhere
//checkentail n >= 0 |- exists f : fib(n,f).

//checkentail 0 >= 0 |- exists f : fib(0,f).

//checkentail 1 >= 0 |- exists f : fib(1,f).

//checkentail n > 1 & forall(m : m < 0 | m >= n | exists(fm : fib(m,fm))) |- exists f : fib(n,f).

// 2) unique image
//checkentail fib(n,f1) & fib(n,f2) |- f1 = f2.

// proof by induction: expand to the following

//checkentail fib(0,f1) & fib(0,f2) |- f1 = f2.

//checkentail fib(1,f1) & fib(1,f2) |- f1 = f2.

//checkentail n > 1 & forall(f1,f2,m : m < 0 | m >= n | !(fib(m,f1)) | !(fib(m,f2)) | f1 = f2)  & fib(n,f1) & fib(n,f2) |- f1 = f2.

// Theorem : for any n >= 0 : F_n <= n!

//checkentail fib(n,f) & fact(n,g) |- f <= g.

checkentail fib(0,f) & fact(0,g) |- f <= g.

checkentail fib(1,f) & fact(1,g) |- f <= g.

checkentail n > 1 & fib(n-1,f1) & fib(n-2,f2) & fact(n-1,g1) & fact(n-2,g2) & f1 <= g1 & f2 <= g2 & fib(n,f) & fact(n,g) |- f = f1 + f2 & g = n * g1 & g1 = (n-1) * g2.

//checkentail n > 1 & fib(n-1,f1) & fib(n-2,f2) & fact(n-1,g1) & fact(n-2,g2) & f1 <= g1 & f2 <= g2 & fib(n,f) & fact(n,g) |- f <= g.

// after removing all relational information, we are left with

//checkentail n > 1 & f = f1 + f2 & 0 <= f1 <= g1 & 0 <= f2 <= g2 & g = g1 * n & g1 = (n-1) * g2 |- f <= g.
