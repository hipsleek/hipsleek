global int stk;

// OK

int clear_foo() 
  requires true
  ensures res=stk' & stk'=0; // & stk'=stk;
{
  stk = 0;
  return stk;
}

