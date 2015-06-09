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
    a[5] = a[5]+1;
    return foo(a); } 
  else {
    int tmp=a[5];
    return tmp;
  }
}

/*
# ex13a.ss 

[RELDEFN Q: ( 1<=(a[5]) & Q(a_1230,a',res) & update_array_1d(a,a_1230,1+(a[5]),5)) -->  Q(a,a',res),
RELDEFN Q: ( a'=a & res=a[5] & (a[5])<=0) -->  Q(a,a',res)]

# below is wrong, as we should have at
   least the condition a[5]<0 for base-case

Post Inference result:
foo$int[]
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [a]
           emp&!(res) & res=a[5] & a=a'&{FLOW,(4,5)=__norm#E}[]
 
*/
