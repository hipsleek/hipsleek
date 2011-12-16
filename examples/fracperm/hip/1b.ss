/* fork(id,method_name,single argument) */

/* test sequential code first */

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
  ensures x::cell<i+1>*y::cell<j+1> & flow __norm; //'
{
  /* {id'=id & x'=x & flow __norm} */
  int id;
  inc(x);
  inc(y);
  dprint;
  return id;
  /* {id'=id & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} */
}

int main() 
  requires true
  ensures res=2;
{ 
  cell x=new cell(0);
  cell y=new cell(0);
  int id;
  id = test(x,y);
  //join(id);
  return x.val+y.val;
}

