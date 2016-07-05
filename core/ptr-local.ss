/*
  2012-04-02: POINTER TRANSLATION
  Address-of local variables
 */

/**********************************************
Original Program
**********************************************/

void inc(int* p)
  requires p::int_ptr<v>
  ensures p::int_ptr<v+1>; //'
{
   (*p) = (*p) + 1;
}

void main()
  requires true
  ensures true;
{
  int x,y;
  x= 7;
  int* p1 =&x;
  inc(p1);
  int* p2;
  p2=&x;
  inc(p2);
  int z = x;
  assert(z'=9); //'
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

/* void main() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int y; */
/*   int_ptr x = new int_ptr(0); */
/*   x.val = 7; */
/*   int_ptr p1 =x; */
/*   inc(p1); */
/*   int_ptr p2; */
/*   p2=x; */
/*   inc(p2); */
/*   int z = x.val; */
/*   assert(z'=9); //' */
/* } */
