global int stk;


// when just reading, why use ref parameter for global

int read_foo() 
  requires true
  ensures res=stk; // & stk'=stk;
{
  return stk;
}

