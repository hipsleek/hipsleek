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
      x >= 1.1    -> requires Term ensures true;
      x <= 1.01      -> requires Loop ensures false;    // wrong specs, should be x <= 1.0
      1.01 < x < 1.1 -> requires Term[Seq{-x, (-infty, -1), -1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1(cube(x));
  }
}

void foo2(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 0.9      -> requires Loop ensures false;
      0.9 < x < 1.1 -> requires Term[Seq{-x, (-infty, -1), -1.1}] ensures true; // wrong specs, should be 1 < x < 1.1
    }
{
  if (x < 1.1)
  {
    foo2(cube(x));
  }
}

void foo3(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x, (-infty, -2), -1.1}] ensures true; // wrong domain, should be (-infty, -1)
    }
{
  if (x < 1.1)
  {
    foo3(cube(x));
  }
}

void foo4(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x, (-100, -1), -1.1}] ensures true; // wrong domain, should be (-infty, -1)
    }
{
  if (x < 1.1)
  {
    foo4(cube(x));
  }
}

void foo5(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x, (-infty, -1), -1.1}] ensures true; // wrong limit
    }
{
  if (x < 1.1)
  {
    foo5(cube(x));
  }
}
