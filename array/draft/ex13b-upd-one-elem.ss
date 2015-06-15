//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  if (a[5]>0) {
    // a[6] = a[6]+1;
    a[5] = a[5]-1;
    return foo(a); } 
  else {
    int tmp=a[5];
    return tmp;
  }
}

/*
# ex13b.ss 

[RELDEFN Q: ( v_int_15_1222=(a[5])-1 & 1<=(a[5]) & Q(a_1231,a',res) & 
update_array_1d(a,a_1231,v_int_15_1222,5)) -->  Q(a,a',res),
RELDEFN Q: ( a'=a & res=a[5] & (a[5])<=0) -->  Q(a,a',res)]
*************************************

!!! **pi.ml#614: Q(a,a',res) = ( a'=a & res=a[5] & (a[5])<=0) \/ ( v_int_15_1222=(a[5])-1 & 1<=(a[5]) & Q(a_1231,a',res) & 
update_array_1d(a,a_1231,v_int_15_1222,5))

What is this?
-------------
*************************************
****** Before putting into fixcalc*******
pre_vars: a___5___,a
post_vars: a___5___',a',res
*************************************
formula:  ((a'=a & res=a[5] & (a[5])<=0) | 
(exists(fc_1234:exists(v_int_15_1222:exists(a_1231:Q(a_1231[5],a_1231,a'[5],a',res) & 
update_array_1d(a,a_1231,v_int_15_1222,fc_1234)) & v_int_15_1222=(a[5])-1) & 
fc_1234=5) & 1<=(a[5])))


Q(a,a',S) = a[5]<=0 & unchanged(a,a',S) & S={} 
             \/  a[5]>0 & Q(a,a',S1) & S=S1+{5}

Q(a,a',S) = a[5]<=0 & unchanged(a,a',S) & S=(a,a' 
             \/  a[5]>0 & Q(a,a',S1) & S=S1+{5}
*/
