/* fork(id,method_name,single argument) */

class e1 extends __Exc{}

data cell {
  int val;
}

void inc(cell x)
  requires x::cell<i>
  ensures x::cell<i+1> & flow __norm; //'
{
  x.val = x.val+1;
}

int test(cell x, cell y)
  requires x::cell<i>* y::cell<j>
  ensures y::cell<j+1> & res=z
          and x::cell<i+1> & thread=z ; //'
{
  /* {id'=id & x'=x & flow __norm} */
  int id;
  /* fork(id,inc,x); */
  return id;
  /* {id'=id & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} */
}

