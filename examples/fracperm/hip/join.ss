/* 
   Working examples - Join
   id=fork(id,method_name,arguments) ;
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

void testjoin(int id, cell x)
  /* requires (exists v: id=v and x'::cell<i+1> & thread=v) //' */
  requires [i] (true) and x::cell<i+1> & thread=id //'
  ensures x::cell<i+1>; //'
{
  join(id);
}

//valid
void test(cell x, cell y)
  requires x::cell<i>* y::cell<j>
  ensures y::cell<j+1> * x::cell<i+1>;
{
  int id;
  id=fork(inc,x); // generate a unique symbolic var for id
  inc(y);
  join(id);
}
