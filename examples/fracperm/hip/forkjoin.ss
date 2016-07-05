/* 
   Working examples
   id=fork(id,method_name,arguments) ;
   join(id);
*/


data cell {
  int val;
}

//valid
void inc(cell x)
  requires x::cell<i>
  ensures x::cell<i+1> & flow __norm; //'
{
  x.val = x.val+1;
}

//valid
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
  inc(y);
  return id;
}

//valid using expl inst
void testjoin(int id, cell x)
  /* requires (exists v: id=v and x'::cell<i+1> & thread=v) //' */
  /* requires (exists i: true and x::cell<i+1> & thread=id) //' */
  requires [i] (true) and x::cell<i+1> & thread=id //'
  ensures x::cell<i+1>; //'
{
  join(id);
}

//valid
int main()
  requires true
  ensures res>=2;
{ cell x=new cell(0);
  cell y=new cell(0);
  int id;
  dprint;
  id = testfork(x,y);
  dprint;
  testjoin(id,x);
  dprint;
  return x.val+y.val;
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
