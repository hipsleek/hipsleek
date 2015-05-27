//hip_include prelude_aux
//#option --ato
//relation P(int a,int r).

relation P(int a,int b,int r).
relation P1(int a,int b).
relation P2(int[] a,int[] b).

void loop(ref int[] a)
  infer[P1,P2]
  requires true
//ensures P1(a[5],a'[5]);
  ensures P2(a,a');
{
  if (a[5]>0) {
     a[5] = a[5] -1;
    return loop(a);
  }
}

/*

[RELDEFN P2: ( a_1225[5]=(a[5])-1 & true & 1<=(a[5]) & P2(a_1225,a')) -->  P2(a,a'),
RELDEFN P2: ( a'[5]=a[5] & (a[5])<=0) -->  P2(a,a')]
*************************************

*/
