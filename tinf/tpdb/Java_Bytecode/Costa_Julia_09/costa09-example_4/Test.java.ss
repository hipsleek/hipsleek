

data Test
{

}
 void Test_exampleMethods(Test _this, ExamplesCont x, Examples y)
{
  int i = 0;
  while (Examples_getF(x.e) > 0) {
    i += Examples_getF(y);
    Examples_setF(x.e, Examples_getF(x.e) - 1);
  }
}

void Test_main(String[] args)
{
  Test o = new Test();
  ExamplesCont x = new ExamplesCont();
  Examples y = new Examples();
  Test_exampleMethods(x, y);
}



data ExamplesCont
{
Examples e;
}
 



data Examples
{
int f = 10;
}
 int Examples_getF(Examples _this)
{
  return _this.f;
}

void Examples_setF(Examples _this, int f)
{
  this_f = f;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;