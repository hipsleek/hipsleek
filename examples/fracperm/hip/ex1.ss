/* id=fork(id,method_name,arguments) ;
   join(id);
*/

data cell {
  int val;
}

void inc(cell x)
  requires x::cell<i>
  ensures x::cell<i+1> & flow __norm; //'
{
  x.val = x.val+1;
}

int testfork(cell x, cell y)
  requires x::cell<i>* y::cell<j>
  ensures y'::cell<j+1> & res=z
          and x'::cell<i+1> & thread=z ; 
//' z may not be existential, 
//it is a global unique symbolic var
{
  int id;
  id=fork(inc,x); // generate a unique symbolic var for id
  inc(y);
  return id;
}

void testjoin(int id, cell x)
  /* requires (exists v: id=v and x'::cell<i+1> & thread=v) //' */
  requires true and x'::cell<i+1> & thread=id) //'
  ensures x'::cell<i+1>; //'
{
  join(id);
}

int main()
  requires true
  ensures res=2;
{ cell x=new cell(0);
  cell y=new cell(0);
  int id;
  id = testfork(x);
  testjoin(id,x);
  return x.val+y.val;
}
