//hip_include prelude_aux
//#option --ato
relation P(int a,int r).

int foo2(ref int[] a,int haha)
  infer[P]
  requires true
  ensures P(a[5],res);
//ensures (a[5]>=5 & res=a[5]+6) | (a[5]<5 & res=11);
//ensures (a[5]>=5 & res=a[5]+6 & a'[5]=a[5]) | (a[5]<5 & a'[5]=5 & res=11);
{
  if (a[5]<5) {
    //a = update_arr(a,5,0);
    a[5] = a[5]+1;
    return foo2(a,haha);
  }
  else{
    return a[5]+6;
  }
}
