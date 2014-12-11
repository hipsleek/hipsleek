data cell {
  int val;
}

bool rand()
  requires true
  ensures !res or res;

int foo()
  //infer [@leak]
  requires emp  ensures emp;
{
  cell x;
  x=new cell(5);
  return x.val;
}

/*
# ex2-leak.ss --classic

We obtained a post-cond failure:

Procedure foo$ FAIL.(2)
Exception Failure("Post condition cannot be derived.") Occurred!

I wonder if we can change it to a:

  "memory leak failure : residue forbiddne"

Checking procedure foo$... 
Post condition cannot be derived:
  (must) cause:  x_1361::cell<v_int_14_1358>&v_int_14_1358=5 & 
v_int_15_1342'=v_int_14_1358 & res=v_int_15_1342'&{FLOW,(4,5)=__norm#E}[]: residue is forbidden.(2)

*/
