relation P(int a,int b,int r).
  relation P1(int[] a,int[] b).
  relation P2(int[] a,int[] b,int r).

int loop(ref int[] a)
//infer[@post_n]
  infer[@arrvar,P2]
  requires true
  ensures P2(a,a',res);
{
  while(a[5]>0)
    infer[@arrvar,P1,update_array_1d]
    requires true
      ensures P1(a,a');
  {
    a[5] = a[5]-1;
    a[6] = a[6]+1;
  }
  return a[6];

}
