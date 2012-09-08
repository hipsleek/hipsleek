/*
  cube example: x' = x * x * x
      void foo1{
        if (x < 1.1)
        {
          foo1(x*x*x);
        }
      }
*/

float cube(float x)
  requires Term
  ensures res = __pow(x,3);      // __pow(x) is the built-in function

// correct specs -> proving OK!
void foo1a(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x@(-infty, -1), -1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1a(cube(x));
  }
}

// correct specs -> proving OK!
void foo1b(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x@(-infty, -1), x < 1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1b(cube(x));
  }
}

// INVALID SPECS: inappropriate domain 
void foo1c(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x@(-infty, -2), x < 1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1c(cube(x));
  }
}

// INVALID SPECS: inappropriate domain 
void foo1d(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x@(-100, -1), x < 1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1d(cube(x));
  }
}

// INVALID SPECS: inappropriate loop condition 
void foo1e(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[Seq{-x@(-infty, -1), x < 0.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1e(cube(x));
  }
}

