
void loop(ref int x, ref int y, int N)
 case {
  x>N ->  
     // variance 0 ==> true
     ensures "l1":x'=x & y'=y;
  x<=N -> 
 case { 
    y>N ->
      // variance 0 ==> x>N
      ensures "l2":true;
    y<=N -> 
      // variance -(x+y)@(-2*N-1)
      ensures "l3":true;
  }
 }
{
  if (x<=N) {
    x=x+1;
    assert "l2": y'>N;
    assert "l3": -(x+y)+(x'+y')>0;
    assert "l3": -(x'+y')-(-2*N-1) >= 0;
    loop(y,x,N);
  }
}

