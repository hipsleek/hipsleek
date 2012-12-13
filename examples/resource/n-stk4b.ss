global int stk;

// OK

int clear_foo() 
  requires true
  ensures res=stk & stk'=0; //'
{
  int v=stk;
  stk = 0;
  return v;
}

void main() 
  requires true
  ensures stk'=0; // & stk'=stk;
{
  int v=clear_foo();
}
