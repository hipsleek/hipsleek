

data TypeSwitch
{

}
 void TypeSwitch_main(String[] args)
{
  A x = null;
  switch (args.length) {
    case 0:
      x = new A();
      break;
    case 1:
      x = new B();
      break;
    case 2:
      x = new C();
      break;
  }
  while (A_hasSuperType()) {
    x = A_getSuperType();
  }
}



data C
{

}
 A C_getSuperType(C _this)
{
  return new B();
}



data B
{

}
 boolean B_hasSuperType(B _this)
{
  return true;
}

A B_getSuperType(B _this)
{
  return new A();
}



data A
{

}
 boolean A_hasSuperType(A _this)
{
  return false;
}

A A_getSuperType(A _this)
{
  return null;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;