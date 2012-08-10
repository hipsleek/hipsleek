/*
  cube examples 
*/

//---- hip ----

float cube(float x)
  requires Term
  ensures res = __pow(x,3);      // __pow(x) is the built-in function

void foo1(float x)
    case
    {
      x >= 1.1      -> requires Loop ensures false;
      0.1 < x < 1.1 -> requires Term[SeqDec{x, (0.0, 1.0), 0.1}] ensures true; // wrong specs, should be 0.1 < x < 1.0
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo1(cube(x));
  }
}

void foo2(float x)
    case
    {
      x >= 0.9      -> requires Loop ensures false; // wrong specs, should be x >= 1.0
      0.1 < x < 0.9 -> requires Term[SeqDec{x, (0.0, 1.0), 0.1}] ensures true;
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo2(cube(x));
  }
}

void foo3(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 < x < 1.0 -> requires Term[SeqDec{x, (0.0, +infinity), 0.1}] ensures true; // domain should be (0.0, 1.0)
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo3(cube(x));
  }
}

void foo4(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 < x < 1.0 -> requires Term[SeqDec{x, (0.0, 1.1), 0.1}] ensures true; // domain should be (0.0, 1.0)
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo4(cube(x));
  }
}

void foo5(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 < x < 1.0 -> requires Term[SeqDec{x, (0.01, 1.0), 0.1}] ensures true; // domain should be (0.0, 1.0)
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo5(cube(x));
  }
}

void foo6(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 < x < 1.0 -> requires Term[SeqDec{x, (-0.01, 1.0), 0.1}] ensures true; // domain should be (0.0, 1.0)
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo6(cube(x));
  }
}

void foo7(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 < x < 1.0 -> requires Term[SeqDec{x, (-infinity, 1.0), 0.1}] ensures true; // domain should be (0.0, 1.0)
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo7(cube(x));
  }
}

void foo8(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 < x < 1.0 -> requires Term[SeqDec{x, (0.0, 1.0), 0.1}] ensures true; // limit should be 0.0
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo8(cube(x));
  }
}
