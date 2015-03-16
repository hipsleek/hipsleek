void loop(ref int[] a)
  infer[@post_n]
  requires true
  ensures true;
  /* requires a[5]>=0 */
  /* ensures a'[5]=0; */
{
  dprint;
  if (a[5]>0) {
    a[5]=a[5]-1;
    dprint;
    loop(a);
    dprint;
  }
 dprint;
}

/* void loop(ref int[] a) */
/* //infer[@post_n] */
/*   requires true */
/*   ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a[5]=a'[5]); */
/* { */
/*   if (a[5]>0) { */
/*     a[5]=a[5]-1; */
/*     loop(a); */
/*   } */
/* } */



/* void loop2(ref int a) */
/*   //infer[@post_n] */
/*   requires a>=0 */
/*   ensures a'=0; */
/* { */
/*   if (a>0) { */
/*     a=a-1; */
/*     loop2(a); */
/*   } */
/* } */

