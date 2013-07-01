/*
  Pointer translation: Addressable reference paramters
  of fork procedures.
  Case 2 : addresable inside fork procedure
 */

/**********************************************
Original Program
**********************************************/
void inc(int* i)
  requires i::int_ptr<v>
  ensures i::int_ptr<v+1>;
{
  (*i) = (*i) +1 ;
}

void addr(ref int x)
  requires x=5
  ensures x'=6; //'
{
  int* p = &x;
  inc(p);
  int z=x;
  assert (z'=6); //'
}

void main()
  requires true
  ensures true;
{  int x;
   x=5;
   addr(x);
   int z = x;
   assert(z'=6); //'
}


/**********************************************
Translated Program
**********************************************/
/* void inc(int_ptr i) */
/*   requires i::int_ptr<v> */
/*   ensures i::int_ptr<v+1>; */
/* { */
/*   i.val = i.val +1 ; */
/* } */

/* void addr(int_ptr x) */
/*   requires x::int_ptr<5> */
/*   ensures x::int_ptr<6>; //' */
/* { */
/*   int_ptr p = x; */
/*   inc(p); */
/*   int z = x.val; */
/*   assert (z'=6); //' */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* { int_ptr x = new int_ptr(0); */
/*   x.val = 5; */
/*   addr(x); */
/*   int z = x.val; */
/*   assert(z'=6); //' */
/*   delete(x); */
/* } */

