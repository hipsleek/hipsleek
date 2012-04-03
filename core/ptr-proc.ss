/*
  2012-04-02: POINTER TRANSLATION
  When address-of variable "x" is passed to a
  procedure (inc).
  int x;
  ...&x...
  inc(x);
 
  
 */

/**********************************************
Original Program
**********************************************/

void inc(ref int x,int y)
  requires true
  ensures x'=x+y; //'
{
  x=x+y;
}

void main()
  requires true
  ensures true;
{
  int x = 7;
  int y=0;
  int* ptr = &x;
  inc(x,y+1);
  int z = x;
  assert(z'= 8); //' TODO
}

/**********************************************
Translated Program
**********************************************/
/* void inc(ref int x,int y) */
/*   requires true */
/*   ensures x'=x+y; //' */
/* { */
/*   x=x+y; */
/* } */

/* void inc_aux_1(int_ptr ptr_x) */
/*   requires ptr_x::int_ptr<x> */
/*   ensures ptr_x::int_ptr<x_new> & x_new=x+y; //' */
/* { */
/*   int aux = ptr_x.val; */
/*   inc(aux); */
/*   ptr_x.val = aux; */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int_ptr x = new int_ptr(7); */
/*   int y = 7; */
/*   int_ptr ptr = x; */
/*   inc_aux_1(x,y+1); */
/*   int z = x.val; */
/*   assert(z'= 8); */
/* } */
