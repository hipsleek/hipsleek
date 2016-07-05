void foo2(ref int[] a)
  requires true
  ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]);
{
  if (a[5]>0) {
    //a = update_arr(a,5,0);
    a[5] = a[5]-1;
    foo2(a);
  }
}

void foo3(ref int[] a,int i)
  requires i<10
  ensures forall(k:(!(10>k>=i & i>=0) | a[k]=0));// 10>k>=i>0
{
  if (i>=0){
    //a = update_arr(a,5,0);
    a[i] = 0;
    foo3(a,i-1);
  }
}

