/* relation P(int[] a). */
/* relation Q(int[] a,int[] b,int r). */

/* int foo(ref int[] a) */
/*   infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res); */
/* { */
/*   if (a[5]>0) { */
/*     a[5] = a[5]-1; */
/*     return foo(a); } */
/*   else { */
/*     return a[5]; */
/*   } */
/* } */


//hip_include prelude_aux
//#option --ato
//relation P(int a,int r).

relation P2(int[] a,int[] a_prime,int i).


void foo2(ref int[] a,int i)
  infer[P2, update_array_1d]
  requires i>=0
  ensures P2(a,a',i);
{
  if (i<10) {
    //a = update_arr(a,5,0);
    a[i] = 5;
    foo2(a,i+1);
  }
}

/*

[RELDEFN P2: ( 0<=i & i<=9 & P2(a_1419,a',1+i) & update_array_1d(a,a_1419,5,i)) -->  P2(a,a',i),
RELDEFN P2: ( a'=a & 10<=i) -->  P2(a,a',i)]

*/

void foo3(ref int[] a,int i)
  requires i<10 & (forall(k:(!(10>k>i) | a[k]=0)))
  ensures (i<0 & forall(k:(!(10>k>=0) | a'[k]=0)))|(i>=0 & forall(k:(!(10>k>=i) | a'[k]=0)));// 10>k>=i>0
{
  if (i>=0){
    //a = update_arr(a,i,0);
    a[i] = 0;
    foo3(a,i-1);
  }
}

void foo4(ref int[] a,int i)
  requires true //(forall(k:(!(k>i) | a[k]=0)))
  ensures (i<0 | (i>=0 & forall(k:(!(0<=k<=i) | a'[k]=0)));// 10>k>=i>0
{
  if (i>=0){
    //a = update_arr(a,i,0);
    a[i] = 0;
    foo4(a,i-1);
  }
}

