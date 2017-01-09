//pred_prim read<b:bag(int)>;

pred_prim read<b:int>;

int read_arr(int[] a, int i)
  requires a::read<j>@L & j=i
  ensures  res=a[i];

int foo2(int[] a)
  requires a::read<5>@L
  ensures res=a[5]+5;
{ 
  int v=read_arr(a,5);
  return v+5;
}

/*
# ex8a2.ss --ato

# reading only


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
