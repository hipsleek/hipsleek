
// 90 -> 91
relation postA(int n, int r).
relation postB(int n, int r).

int f91(int n)
  infer[@post_n,@term]
 case {
  n>=91 ->  ensures true;
  n<91 -> ensures true;
 }
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*
# rec-f91a1.ss

Why is this solution difference from rec-f91.ss?
Would it not be better to use mutual-recursion?



*/
