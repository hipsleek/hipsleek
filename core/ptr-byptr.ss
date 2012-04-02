/*
  Pointer translation: pass-by-pointer
 */

/**********************************************
Translated Program
**********************************************/
/* void inc(int_ptr i) */
/*   requires i::int_ptr<v> */
/*   ensures i::int_ptr<v+1>; */
/* { */
/*   i.val = i.val +1 ; */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* { int_ptr x = new int_ptr(0); */
/*   x.val = 5; */
/*   int_ptr p ; */
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
  requires i::int_ptr<v>
  ensures i::int_ptr<v+1>;
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
