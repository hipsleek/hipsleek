//hip_include prelude_aux
//#option --ato
//relation P(int a,int r).

relation P2(int a,int a_prime,int r).

int foo2(ref int[] a)
  infer[P2]
  requires true
//ensures P(a[5],res);
  ensures P2(a[6],a'[6],res);
//ensures (a[5]>=5 & res=a[5]+6) | (a[5]<5 & res=11);
//ensures (a[5]>=5 & res=a[5]+6 & a'[5]=a[5]) | (a[5]<5 & a'[5]=5 & res=11);
{
  if (a[6]<5) {
    //a = update_arr(a,5,0);
    a[6] = a[6]+1;
    return foo2(a);
  }
  else{
    return a[6]+6;
  }
}

int foo3(ref int a)
  infer[P2]
  requires true
//ensures P(a[5],res);
  ensures P2(a,a',res);
//ensures (a[5]>=5 & res=a[5]+6) | (a[5]<5 & res=11);
//ensures (a[5]>=5 & res=a[5]+6 & a'[5]=a[5]) | (a[5]<5 & a'[5]=5 & res=11);
{
  if (a<5) {
    //a = update_arr(a,5,0);
    a = a+1;
    return foo3(a);
  }
  else{
    return a+6;
  }
}
