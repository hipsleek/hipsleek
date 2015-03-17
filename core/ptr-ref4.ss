/*
  Example of addresable reference parameters.
  Need to maintain poin-to fact (i.e. p=&x)
  in an inter-procedural manner.
  Note: addresable varible (x) that is passed by reference
  vs addresable variable (y) that is passed by value
 */


void inc(int* i)
  requires i::int_ptr<v>
  ensures i::int_ptr<v+1>;
{
  (*i) = (*i) + 1;
}

/*
  need to maintain point-to fact even after
  going out of scope of initialize
*/
void initialize(ref int_ptr p, ref int x,int y)
  requires p::int_ptr<y>
  ensures p'::int_ptr<x'> * p::int_ptr<y> & x'=x+y; //'
{
  x = x + y;
  p=&x;
}

void main()
  requires true
  ensures true;
{
  int x = 7;
  int y = 9;
  int* p = &y;
  /* dprint; */
  initialize(p,x,y);
  /* dprint; */
  inc(p);
  int z = x;
  assert(z'=17); //' 7 + 9 + 1
}

/**********************************************
Translated Program
**********************************************/
/* void inc(int_ptr i) */
/*   requires i::int_ptr<v> */
/*   ensures i::int_ptr<v+1>; */
/* { */
/*   i.val = i.val + 1; */
/* } */


/* void main() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int_ptr x = new int_ptr(7); */
/*   int_ptr y = new int_ptr(9); */
/*   int_ptr p = y; */
/*   initialize(p,x,y.val); */
/*   inc(p); */
/*   int z = x.val; */
/*   assert(z'=17); //' 7 + 9 + 1 */
/*   delete(x); */
/*   delete(y); */
/* } */

/* void initialize(ref int_ptr p, int_ptr x, int y) */
/*   requires x::int_ptr<old_x> * p::int_ptr<y> */
/*   ensures x::int_ptr<new_x> * p::int_ptr<y> & new_x=old_x+y & p'=x; //' */
/* { */
/*   x.val = x.val + y; */
/*   p=x; */
/* } */
