// need a new type, called thread which can be 
// an object type
// need a new fork operator
// need a new join operator which can be 
//   implemented using a more general non-lexical catch

data cell{
  int val;
}

void inc(cell x) 
     requires x::cell<n>
     ensures x::cell<n+1> ; //'
{
  x.val ++;
}

void test(cell x,  cell y)
     requires x::cell<n1> * y::cell<n2>
     ensures x::cell<n1+1> * y::cell<n2+1>; 
{
    thread t = fork inc(x); //model a fork
    assert x'::cell<n1+1>; //' fail
    inc(y);
    assert y'::cell<n2+1>; //' ok
    join(t);
    assert x'::cell<n2+1>; //' ok
}
