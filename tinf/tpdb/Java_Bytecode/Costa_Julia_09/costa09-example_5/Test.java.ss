

data Test
{

}
 void Test_main(String[] args)
{
  Loops3 o1 = new Loops3();
  Loops3 o2 = o1;
  Loops3_m(10, o2);
}



data Loops3
{

}
 void Loops3_m(Loops3 _this, int n, Loops3 x)
{
  while (_this.i < n) {
    _this.i++;
    x.i--;
  }
}



data Loops2
{
int i;
}
 void Loops2_m(Loops2 _this, int n)
{
  while (_this.i < n) {
    _this.i++;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;