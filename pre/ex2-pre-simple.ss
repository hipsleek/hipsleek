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

*/
