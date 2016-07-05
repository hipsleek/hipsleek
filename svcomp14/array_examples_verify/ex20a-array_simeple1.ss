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
    int i =5;
    a[i] = x+1;
    dprint;
    r = a[i];
    dprint;
    //dprint;
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

 State:(exists a_37':int[]: 
  htrue&r_36':int=a_37':int[][5] & 5<=ahaub_1349:int & ahalb_1348:int<=5 & dom:RelT([])(a_37':int[],ahalb_1348:int,ahaub_1349:int) & ahaub:int=ahaub_1349:int & ahalb:int=ahalb_1348:int & update_array_1d:RelT([])(a_1347:int[],a_37':int[],1+x':int,5) & dom:RelT([])(a_37':int[],ahalb:int,ahaub:int) & 5<=ahaub:int & ahalb:int<=5 & dom:RelT([])(a_1347:int[],ahalb:int,ahaub:int) & x':int=x:int&{FLOW,(4,5)=__norm#E})


 htrue&
(exists(i:
        exists(a_1187:exists(a_1189:a_1189[5]=a_1187[i] & a_1189[i]=a_1187[i]) & x+1=a_1187[i] & res=a_1187[i]))
 | (exists(a_1189:exists(i:exists(a_1187:a_1189[i]=a_1187[i]) & i!=5) & a_1189[5]=1+x) & res=1+x))
&{FLOW,(4,5)=__norm#E}[]

*/



