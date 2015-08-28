int read_arr(int[] a, int i)
  requires a::read<{i}> 
  ensures  res=a[i];
  requires a::write<{i}> 
  ensures  res=a[i];

void update_arr(int[] a, int i,int v)
  requires a::write<{i}> 
  ensures  a'[i]=v;

void foo2(ref int[] a)
  requires a::write<{5}>@L
  ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]) 
  ;
{ 
  int v=read_arr

  if (a[5]>0) {
    //a = update_arr(a,5,0);
    a[5] = 0;
    foo2(a);
  }
}

/*
# ex8a1.ss --ato

new array logic

 a::read<S1> declares that S1 is a finite set of addresses
  that would be read-only
 a::write<S2> declares that S2 is a finite set of addresses
  that would be read-write

We would then model each array a by
All other elements would be unchanged.

We then model each array A by S1 read-only var,
and S2 ref vars.

We also make sure the two sets are disjoint by the following

   a::read<S1>*a::write<S2> & S1/\S2!={] ==> false
   a::read<S1 U S2>  == a::read<S1> * a::read<S2>
   a::write<S1 U S2> == a::write<S1> * a::write<S2>

*/
