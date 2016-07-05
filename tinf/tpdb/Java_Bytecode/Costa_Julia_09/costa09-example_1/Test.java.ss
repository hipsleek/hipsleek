

data Test
{

}
 int Test_add(Test _this, int n, A o)
{
  int __res = 0;
  int i = 0;
  while (i <= n) {
    __res = __res + i;
    i = A_incr(o, i);
  }
  return __res;
}

void Test_main(String[] args)
{
  int test = 1000;
  Test testClass = new Test();
  A a = new A();
  int result1 = Test_add(test, a);
  a = new B();
  int result2 = Test_add(test, a);
  a = new C();
  int result3 = Test_add(test, a);
}



data C
{

}
 int C_incr(C _this, int i)
{
  return i = i + 3;
}



data B
{

}
 int B_incr(B _this, int i)
{
  return i = i + 2;
}



data A
{

}
 int A_incr(A _this, int i)
{
  return i = i + 1;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;