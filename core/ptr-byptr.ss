/*
  Pointer translation: pass-by-pointer
 */

/**********************************************
Translated Program
**********************************************/
/* void inc(integer i) */
/*   requires i::integer<v> */
/*   ensures i::integer<v+1>; */
/* { */
/*   i.val = i.val +1 ; */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* { integer x = new integer(0); */
/*   x.val = 5; */
/*   integer p ; */
/*   p = x; */
/*   inc(p); */
/*   int z = x.val; */
/*   assert(z'=6); //' */
/*   delete(x); */
/* } */

/**********************************************
Original Program
**********************************************/
void inc(int *i)
  requires i::integer<v>
  ensures i::integer<v+1>;
{
  (*i) = (*i) + 1;
}

void main()
  requires true
  ensures true;
{
  int x;
  x= 5;
  int *p;
  p =&x;
  inc(p);
  int z=x;
  assert(z'=6); //'
}
