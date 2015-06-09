relation P(int a,int b,int r).
  relation P1(int a,int b,int c,int d).
  relation P2(int a,int b,int c,int d,int r).

  int loop(ref int a_5,ref int a_6)
//infer[@post_n]
  infer[@arrvar,P2]
  requires true
  ensures P2(a_5,a_5',a_6,a_6',res);
{
  while(a_5>0)
    infer[@arrvar,P1,update_array_1d]
    requires true
      ensures P1(a_5,a_5',a_6,a_6');
  {
    a_5 = a_5-1;
    a_6 = a_6+1;
  }
  return a_6;

}
