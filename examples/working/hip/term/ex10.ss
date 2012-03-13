
void loop(ref int x, ref int y, int N)
 case {
  x>N ->  
    requires Term // Base case
    ensures "l1": x'=x & y'=y;
  x<=N -> 
    case { 
      y>N ->
        requires Term // ==> x'>N
        ensures "l2": true;
      y<=N -> 
        requires Term[2*N - (x+y)]
        ensures "l3":true;
  }
 }
{
  if (x<=N) {
    x=x+1;
    //assert "l2": y'>N;
    //assert "l3": -(x+y)+(x'+y')>0;
    //assert "l3": -(x'+y')-(-2*N-1) >= 0;
    loop(y,x,N);
  }
}

