/* fork(id,method_name,single argument) */

class e1 extends __Exc{}

class Thread extends __Exc{
  int id
}

void inc(ref int x)
requires true & flow __norm
ensures x'=x+1 & flow __norm; //'
{
  x++;
}


global int x;
global int y;
global int id;
global int id1;
global int id2;

/* ================= */
/* ==== 1 thread === */
/* ================= */

thread test(ref int x)
requires true & flow __norm
ensures true & flow_norm
    and eres::Thread<res> & x'=x+1 & flow thread; //'
{
  /* {id'=id & x'=x & flow __norm} */
  thread id;
  id = fork inc(x);
  return id;
  /* {id'=id & x'=x & flow __norm */
  /* and eres::thread<id'> & id'=id & x'=x+1 & flow thread;} */
}

int main() 
  requires true
  ensures res=2;
{ int x=0;
  int y=0;
  thread id = test(x);
  inc(y);
  join(id);
  return x+y;
}

