global int stk;


// when just reading, why use ref parameter for global

int read_foo() 
  requires true
  ensures res=stk; // & stk'=stk;
{
  return stk;
}
int clear_foo() 
  requires true
  ensures res=stk' & stk'=0; // & stk'=stk;
{
  stk = 0;
  return stk;
}
void subt_foo2(int n) 
  requires stk>=n
  ensures stk'=stk-n; //'
