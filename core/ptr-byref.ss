/*
  Pointer translation: pass-by-ref
 */


/**********************************************
Original Program
**********************************************/
void inc(int* i)
  requires i::integer<v>
  ensures i::integer<v+1>;
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
{  int x;
   x=5;
   addr(x);
   assert(x'=6); //'
}


/**********************************************
Translated Program
**********************************************/
/* void inc(integer i) */
/*   requires i::integer<v> */
/*   ensures i::integer<v+1>; */
/* { */
/*   i.val = i.val +1 ; */
/* } */

/* void addr(ref int x) */
/*   requires x=5 */
/*   ensures x'=6; //' */
/* { integer x_t = new integer(x); */
/*   integer p = x_t; */
/*   inc(p); */
/*   int z = x_t.val; */
/*   assert (z'=6); //' */
/*   x = x_t.val; */
/*   delete(x_t); */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* { int x; */
/*   x = 5; */
/*   addr(x); */
/*   assert(x'=6); //' */
/* } */

