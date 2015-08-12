void foo2(ref int[] a)
  requires true
  ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]) 
   // & change(a,{5})
   //&  forall(i: i!=5 | a'[i]=a[i])
           ;
{ 
  if (a[5]>0) {
    //a = update_arr(a,5,0);
    a[5] = 0;
    foo2(a);
  }
}

/*
# ex8a.ss --ato

Why is --ato not working?

ERROR: at ex8a-simple3.ss_3:10_3:53
Message: Post condition cannot be derived.

int read_arr(int[] a, int i)
  requires a::read<S> & i in S
  ensures  res=a[i]

int write_arr(int[] a, int i, int val)
  requires a::write<S> & i in S
  ensures  a'[i]=val

*/
