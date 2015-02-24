/*
  Example of addresable reference parameters.
  Need to maintain poin-to fact (i.e. p=&x)
  in an inter-procedural manner.
  Note: scope of a reference paramters is out
  side its procedure, backward until the place
  it is declared.
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
void initialize(ref int_ptr p, ref int x)
  requires true
  ensures p'::int_ptr<x'> & x'=x; //'
{
  p=&x;
}

void main()
  requires true
  ensures true;
{
  int x = 7;
  int* p;
  //dprint;
  initialize(p,x);
  //dprint;
  inc(p);
  int z = x;
  assert(z'=8); //'
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
/*   int_ptr p; */
/*   initialize(p,x); */
/*   inc(p); */
/*   int z = x.val; */
/*   assert(z'=8); //' */
/*   delete(x); */
/* } */

/* void initialize(ref int_ptr p, int_ptr x) */
/*   requires x::int_ptr<old_x> */
/*   ensures x::int_ptr<new_x> & new_x = old_x & p'=x; //' */
/* { */
/*   p=x; */
/* } */
