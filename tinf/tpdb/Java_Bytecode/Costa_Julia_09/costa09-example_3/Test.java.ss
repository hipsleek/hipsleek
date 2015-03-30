

data Test
{
int i;
}
 void Test_m(Test _this, int n)
{
  while (_this.i < n) {
    _this.i++;
  }
}

void Test_main(String[] args)
{
  Test o = new Test();
  Test_m(10);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;