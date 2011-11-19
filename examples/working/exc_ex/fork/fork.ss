data node {
        int val; 
        node next;      
}

data int2{
  int val;
}

class fork_exc extends __Exc {}


/* //simple fork example ' */
/* void test_fork(ref int2 x,  ref int2 y) */
/*      requires x::int2<n1> * y::int2<n2> & f=1.0 */
/*      ensures x'::int2<n1+1> * y'::int2<n2+1>; //' */
/* { */
/*   tid id; */
/*   fork(id,inc,x); // not supported yet */
/*   y.val++; */
/*   join1(id); // not supported yet */
/* } */

void inc(ref int2 x) throws fork_exc
     requires x::int2<n>
     ensures x'::int2<n+1> & flow fork_exc ; //'
{
  x.val ++;
  raise (new fork_exc()); //so that it can be caught at join
}

/* void main(ref int2 x) */
/*      requires x::int2<n> */
/*      ensures x'::int2<n+2>; //' */
/* { */
/*   try{ */
/*     inc(x); */
/*   } */
/*   catch (fork_exc exc){ */
/*     x.val ++; */
/*   }; */

/* } */


void test(ref int2 x,  ref int2 y)
     requires x::int2<n1> * y::int2<n2>
     ensures x'::int2<n1+1> * y'::int2<n2>; //'
{
  try{
    inc(x); //model a fork
    y.val++;
    assert x'::int2<n1>; //' unreachable
  }
  catch (fork_exc exc){
    //can not model a join because the execution y.val++ will be ignored
    // need conjunction
    int i; //no_ops
  };

  //assert x'::int2<n1+1>; //'
  //assert y'::int2<n2+1>; //'
  //inc(y);
}
