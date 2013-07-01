/*
  Pointer translation: global var is a pointer
 */


/**********************************************
Original Program
**********************************************/
global int* p;

void inc()
  requires p::int_ptr<v>
  ensures p'::int_ptr<v+1> & p'=p; //'
{
   (*p) = (*p) + 1;
}

void main()
  requires true
  ensures true;
{ int x;
   x= 5;
   p =&x;
   inc();
   int z=x;
   assert(z'=6); //'
}

/**********************************************
Translated Program
**********************************************/

/* global int_ptr p; */

/* void inc() // ghost "ref int_ptr p" will be added */
/*   requires p::int_ptr<v> */
/*   ensures p'::int_ptr<v+1> & p'=p; //' */
/* { */
/*   p.val = p.val +1 ; */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* {  */
/*   int_ptr x = new int_ptr(0); */
/*   x.val = 5; */
/*   p = x; */
/*   inc(); //ghost "p" will be added */
/*   int z = x.val; */
/*   assert (z'=6); //' */
/*   delete(x); */
/* } */


