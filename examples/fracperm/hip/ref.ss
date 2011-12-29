/* 
   Working examples
   id=fork(id,method_name,arguments) ;
   join(id);
*/


data cell {
  int val;
}

void incInt(ref int x)
  requires true
  ensures x'=x+1; //'
{
  x++;
}

//valid
void inc(ref cell x)
  requires x::cell<i>
  ensures x'::cell<i+1> & flow __norm; //'
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
  id=fork(inc,x); // generate a unique symbolic var for id
  inc(y);
  dprint;
  join(id);
  return x.val+y.val;
}

int test2()
  requires true
  ensures res=2;
{
  int id;
  int x=0;
  int y=0;
  id=fork(incInt,x); // generate a unique symbolic var for id
  incInt(y);
  dprint;
  join(id);
  dprint;
  return x+y;
}
