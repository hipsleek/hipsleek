class Thread extends __Conj {
  int id;
}

data node {
        int val; 
        node next;      
}

data int2{
  int val;
}


/* data tid{ */
/* } */

void inc(ref int2 x)
     requires x::int2(f)<n> & f=1.0
     ensures x'::int2(f)<n+1>;
     //requires x::int2(f)<n> & f=1.0
     //ensures x'::int2(f)<n+1>;
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
  //assert x'::int2(f)<n1+1>;
  //assert y'::int2(f)<n2+1>;
  //inc(y);
}

/* void fork(ref tid id, proc inc, ref int2 x) */
/*   requires x::int2(f)<n1> & f=1.0 */
/*   ensures x'::int2(f)<n1+1> * id::tid<>; //' */
/* { */
/*   inc(x); */
/*   id = new tid(); */
/* } */

/* void join1(tid id) */
/*   requires id::tid<> */
/*   ensures true; */
/* { */
/*   int i; */
/* } */

//simple fork example '
void test_fork(ref int2 x,  ref int2 y)
     requires x::int2(f)<n1> * y::int2(f)<n2> & f=1.0
     ensures x'::int2(f)<n1+1> * y'::int2(f)<n2+1>; //'
{
  int id;
  fork(id,inc,x); //under construction
  //dprint;
  //inc(x);
  y.val++;
  //assert y'::int2(f)<n2+1>;
  dprint;
  join1(id); // not supported yet
  dprint;
  //assert x'::int2(f)<n1+1>;
  //assert y'::int2(f)<n2+1>;
}
