// !!!! This function need to use -prelude "prelude_aux.ss" 
int foo(int x)
  infer[@post_n]
  requires true
//ensures res=x+1;
  ensures true;
{
  int r;
  {
    int[] a;
    //int a[
    int i =5;
    a[i] = x+1;
    r = a[i];
    dprint;
  };
  dprint;
  return r;
}

/* int foo(int x) */
/*   infer[@post_n] */
/*   requires true */
/* //ensures res=x+1; */
/*   ensures true; */
/* { */
/*   int a; */
/*   int i =5; */
/*   a = x+1; */
/*   int r; */
/*   r = a; */
/*   return r; */

/* } */

/*
# ex20b.ss

Can we simplify exists 

 State:(exists a_37': htrue
& r_36'=a_37'[5] 
& 5<=ahaub_1349 & ahalb_1348<=5 
& dom(a_37',ahalb_1348,ahaub_1349) 
& ahaub=ahaub_1349 & ahalb=ahalb_1348 
& update_array_1d(a_1347,a_37',1+x',5) 
& dom(a_37',ahalb,ahaub) 
& 5<=ahaub & ahalb<=5 
& dom(a_1347,ahalb,ahaub) 
& x'=x
&{FLOW,(4,5)=__norm#E})[]



[]
*/
