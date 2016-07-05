

data Init
{

}
 void Init_m(Init _this)
{
  new A();
}

void Init_n(Init _this)
{
  A_f = 13;
}

void Init_main(String[] args)
{
  new Init()_m();
  new Init()_n();
}


global int A_f;
data A
{

}
 

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;