void loop(ref int[] a)
  requires a[5] > 0
  ensures a'[5] = 0;
{
  //foo2(a);
  while(a[5]>0)
    requires true
    ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]);
    {
      a[5] = a[5] -1;
      //a = update_arr(a,5,a[5]-1);
      
  }

}
