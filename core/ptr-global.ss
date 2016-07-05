/*
  Pointer translation: global var "x" is a primitive value
  and will be "&x"
 */
global int x;

/**********************************************
Original Program
**********************************************/
void inc(int* i)
  requires i::int_ptr<v>
  ensures i::int_ptr<v+1>;
{
  (*i) = (*i) +1 ;
}

void addr()
  requires x=5
  ensures x'=x+1;//'
{
  x=5;
  int* p = &x;
  inc(p);
  int z=x;
  assert (z'=6); //'
}

void main()
  requires true
  ensures true;
{
   x=5;
   addr();
   int z =x;
   assert(z'=6);//'
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

/* void addr() //ghost "ref int x" will be added */
/*   requires x=5 */
/*   ensures x'=x+1; //' */
/* { int_ptr x_t = new int_ptr(x); */
/*   x_t.val = 5; */
/*   int_ptr p = x_t; */
/*   inc(p); */
/*   int z = x_t.val; */
/*   assert (z'=6); //' */
/*   x = x_t.val; */
/* } */

/* void main() */
/*   requires true */
/*   ensures true; */
/* {  */
/*   x = 5; */
/*   addr(); // ghost x will be added */
/*   assert(x'=6); //' */
/* } */



