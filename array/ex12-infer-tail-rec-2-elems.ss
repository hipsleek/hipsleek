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
    a[5] = a[5]-1;
    a[4] = a[4]+1;
    return foo(a); } 
  else return a[4];
}

/*
# ex12.ss 

[RELDEFN Q: ( 
   update_array_1d(a_1252,a_1261,1+(a_1252[4]),4) 
  & v_int_14_1233=(a[5])-1 & 
   1<=(a[5]) & Q(a_1261,a',res) 
   & update_array_1d(a,a_1252,v_int_14_1233,5)) 
   -->  Q(a,a',res),
RELDEFN Q: ( a'[4]=res & a'=a & (a'[5])<=0) -->  Q(a,a',res)]
*


[RELDEFN Q: ( a4=a4'-1 & a5'=a5-1 & 1<=a5 & Q(a4',a5',res)) 
   -->  Q(a4,a5,res),
RELDEFN Q: ( a4=res & a5<=0) -->  Q(a4,a5,res)]


*/
