relation P(int a,int r).

int loop(ref int[] a)
  infer[@post_n]
  requires true
  ensures true;
//requires a[5] > 0
//ensures a'[5] = 0;
{
  //foo2(a);
  int i = 0;
  a[5] = 10;
  while(a[5]>0)
    //requires true
    //ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]);
    infer[@post_n]
      requires true
      ensures P(a[5],a'[5]);
  {
    a[5] = a[5] -1;
  }
  return a[5]-2;

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
