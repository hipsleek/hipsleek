relation P(int a,int b,int r).
relation P1(int a,int b).
relation P2(int[] a,int[] b).

int loop(ref int[] a)
//infer[@post_n]
  infer[P]
  requires true
  ensures P(a[5],a'[5],res);
//requires a[5] > 0
//ensures a'[5] = 0;
{
  //foo2(a);
  int i = 0;
  //a[5] = 10;
  while(a[5]>0)
    //requires true
    //ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]);
    //infer[@post_n]
    infer[P1]
    requires true
    // ensures (((a[5])>=1 & 0=a'[5]) | (0>=(a'[5]) & a'[5]=a[5]));
      ensures P1(a[5],a'[5]);
  {
    a[5] = a[5] -1;
  }
/*
Post Inference result:
while_16_2$int[]
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [a]
           emp&0>=(a'[5])&{FLOW,(4,5)=__norm#E}[]
*/
  return a[5];

}

/* int loop_2() */
/*   infer[@post_n] */
/*   requires true */
/*   ensures true; */
/* //requires a[5] > 0 */
/* //ensures a'[5] = 0; */
/* { */
/*   //foo2(a); */
/*   int i = 0; */
/*   int b = 10; */
/*   while(b>0) */
/*     //requires true */
/*     //ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]); */
/*     infer[@post_n] */
/*       requires true */
/*       ensures true; */
/*     { */
/*       b = b -1; */
/*     } */
/*   return b; */

/* } */
