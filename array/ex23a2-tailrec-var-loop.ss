relation P(int a,int b,int r).
  relation P1(int a,int b).
  relation P2(int[] a,int[] b,int r).


  void wloop(ref int a)
  infer[P1]
    requires true
      ensures P1(a,a');
{
  if (a>0) {
    a=a-1;
    wloop(a);
  }
}

/*
int loop(ref int[] a)
//infer[@post_n]
  infer[P2]
  requires true
  ensures P2(a,a',res);
{
  while(a[5]>0)
    infer[P1,update_array_1d]
    requires true
      ensures P1(a,a');
  {
    a[5] = a[5]-1;
  }
  return a[5];

}
*/
