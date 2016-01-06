relation R(int x).

void loop(ref int i,int n, int s)
  requires i>=n or i>=0 & n<=s
  ensures  false;
{    
  if (i<n) {
    assert 0<=i & i<s;
  }
  loop(i+1,n,s);
}
/*
# ex2.ss

How to infer above pre-condition?


false --> necessary(with NT as a bug)

i>=n or i>=0 & n<=s 
   --> sufficient pre(wo NT)
   --> necessary pre (wo NT)

not(..)
== i<n & not(i>=0 & n<=s)
== i<n & (i<0 | n>s)

*/
