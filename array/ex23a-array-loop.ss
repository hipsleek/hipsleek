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
  }
  return a[5];

}

/*
# ex23a2,ex32a (OK)

[RELDEFN P1: ( v_int_16_1237=(a[5])-1 & 1<=(a[5]) & P1(a_1239,a') & 
update_array_1d(a,a_1239,v_int_16_1237,5)) -->  P1(a,a'),
RELDEFN P1: ( a'=a & (a[5])<=0) -->  P1(a,a')]

!!! fixcalc file name: logs/fixcalc.inf
Post Inference result:
while_11_2$int[]
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [a]
           emp&(((a[5])>=1 & 0=a'[5]) | (0>=(a'[5]) & a=a'))&
           {FLOW,(4,5)=__norm#E}[]

*/
