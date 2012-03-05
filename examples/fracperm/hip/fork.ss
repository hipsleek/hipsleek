data node {
        int val; 
        node next;      
}

data int2{
  int val;
}

void inc(ref int2 x)
     requires x::int2(f)<n> & f=1.0
     ensures x'::int2(f)<n+1>;
{
  x.val ++;
}

//valid'
void test(ref int2 x,  ref int2 y)
     requires x::int2(f)<n1> * y::int2(f)<n2> & f=1.0
     ensures x'::int2(f)<n1+1> * y'::int2(f)<n2+1>; //'
{
  inc(x);
  y.val++;
  assert x'::int2(f)<n1+1>;
  assert y'::int2(f)<n2+1>;
  //inc(y);
}

//simple fork example '
void test_fork(ref int2 x,  ref int2 y)
     requires x::int2(f)<n1> * y::int2(f)<n2> & f=1.0
     ensures x'::int2(f)<n1+1> * y'::int2(f)<n2+1>; //'
{
  tid id;
  fork(id,inc,x); // not supported yet
  y.val++;
  join(id); // not supported yet
  assert x'::int2(f)<n1+1>;
  assert y'::int2(f)<n2+1>;
}
