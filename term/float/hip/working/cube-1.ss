/*
  cube examples 
*/

//---- hip ----

float cube(float x)
  requires Term
  ensures res = __pow(x,3);      // __pow(x) is the built-in function

void foo1a(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x, (-infinity, -1), -1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1a(cube(x));
  }
}

void foo1b(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x, (-infinity, -1), x < 1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1b(cube(x));
  }
}

void foo2a(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x, (0, 1), 0.1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2a(cube(x));
  }
}

void foo2b(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x, (0, 1), 0.1 < x < 1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2b(cube(x));
  }
}

void foo3a(float x)
    case
    {
      x >= 1      -> requires Loop ensures false;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x, (0, 1), 0.1}] ensures true;
    }
{
  if (x > 0.1)
  {
    foo3a(cube(x));
  }
}

void foo3b(float x)
    case
    {
      x >= 1      -> requires Loop ensures false;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x, (0, 1), 0.1 < x < 1}] ensures true;
    }
{
  if (x > 0.1)
  {
    foo3b(cube(x));
  }
}
