global int stk;

/*
void test_stk(int n)
  requires stk>=n
  ensures true;
*/
// why stk not recognized as global?

void test_stk2(int stk,int n)
  requires stk>=n
  ensures true;

// why each global parameter simply marked as ref
// rather than occasionally just read-only;
// why occurrence of global not quite recognized ib
// assert/assume?

int foo(int n) 
  requires stk=5
  ensures res=n+1; // & stk'=stk;
{
  //assert stk'>=2;
  test_stk2(stk,2);
  n =n+1;
  return n;
}

