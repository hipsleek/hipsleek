// McCarthy 91
// 90 -> 91
relation P(int n, int r).
int rec1(int i)
  requires true
  //ensures ((1<=i & 1<=res) | (res=0 & i<=0)); //OK
  ensures ((1<=i & i<=res) | (res=0 & i<=0)); //invalid
  //ensures ((1<=i & 1=res) | (res=0 & i<=0)); //OK
{
  if(i <= 0)return 0;
  return rec1( rec1( rec1(i-2) - 1 )) + 1;
}

/*

*/
