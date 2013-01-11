/*
  2012-04-02: POINTER TRANSLATION
  Pointer of pointer
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
  int x = 7;
  int* ptr = &x;
  int** ptrptr;
  ptrptr = &ptr;
  inc(*ptrptr);
  int z = x;
  assert(z'= 8);
}

