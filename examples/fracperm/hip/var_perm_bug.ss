/* 
   Buggy examples
*/


data cell {
  int val;
}

//valid
void inc(cell x)
  requires x::cell<i>
  ensures x::cell<i+1>;
{
  x.val = x.val+1;
}

int test1()
  requires true
  ensures res=2;
{
  int id;
  cell x=new cell(0);
  cell y=new cell(0);
  /* { {x,y}@F } */
  id=fork(inc,x); // x is pass-by-value
  /* { {x,y}@F & y::cell<0> and x::cell<1>} */

  /* x.val =2; //this operation can not be done because  */
  /* //we do not own the heap of x */

  // but this is possible because we have x@F
  x = new cell(2); // BUG: how to prevent this to happen
  // we can avoid this situation by passing x by ref to fork

  inc(y);
  /* { {x,y}@F & y::cell<1> * x::cell<2> and x::cell<1>} */
  join(id); // what is the value of cell x now???
  /* { {x,y}@F & y::cell<1> * x::cell<?>} */
  return x.val+y.val; //currently, y.val=2
}
