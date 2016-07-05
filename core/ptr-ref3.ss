/*
  Pointer translation: Addressable reference paramters
  of fork procedures.
  Case 1 : addresable before fork
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

void main2()
  requires true
  ensures true;
{
  int x = 7;
  int y=0;
  int* ptr = &x;
  int id = fork(inc,x,1);
  /* y = *ptr; //racy --> fail */
  join(id);
  inc(y,2);
  int z = x;
  assert(z'= 8); //'
  int z2 = y;
  assert(z2'= 2); //'
}

/**********************************************
Translated Program
**********************************************/
/* void inc(int_ptr x,int y) */
/*   requires x::int_ptr<old_x> */
/*   ensures x::int_ptr<new_x> & new_x= old_x+y; //' */
/* { */
/*   x.val=x.val+y; */
/* } */

/* void main2() */
/*   requires true */
/*   ensures true; */
/* { */
/*   int_ptr x = new int_ptr(7); */
/*   int_ptr y = new int_ptr(0); */
/*   int id = fork(inc,x,1); */
/*   /\* y.val = ptr.val; //racy --> fail *\/ */
/*   join(id); */
/*   int z = x.val; */
/*   assert(z'= 8); */
/*   inc(y,2); */
/*   int z2 = y.val; */
/*   assert(z2'= 2); //' */
/*   delete(x); */
/*   delete(y); */
/* } */
