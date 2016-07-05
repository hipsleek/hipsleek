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

// valid
int testfork(cell x, cell y)
  requires x::cell<i>* y::cell<j>
  ensures y::cell<j+1> & res=z
          and x::cell<i+1> & thread=z ;
// NOTE: call-by-value parameters & existential vars should not be primed
//' z may not be existential,
//it is a global unique symbolic var
{
  int id;
  id=fork(inc,x); // generate a unique symbolic var for id
  dprint;
  inc(y);
  return id;
}
