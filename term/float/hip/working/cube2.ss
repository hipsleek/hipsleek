/*
  cube example: x' = x * x * x
      void foo2{
        if ((0.1 < x) && (x < 1))
        {
          foo2(x*x*x);
        }
      }
*/

float cube(float x)
  requires Term
  ensures res = __pow(x,3);      // __pow(x) is the built-in function

// CORRECT SPECS
void foo2a(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x@(0, 1), 0.1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2a(cube(x));
  }
}

// CORRECT SPECS
void foo2b(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x@(0, 1), 0.1 < x < 1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2b(cube(x));
  }
}

// INVALID SPECS: inappropriate domain
void foo2c(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x@(-1.0, 1), 0.1 < x < 1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2c(cube(x));
  }
}

// INVALID SPECS: inappropriate domain
void foo2d(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x@(0, +infty), 0.1 < x < 1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2d(cube(x));
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2e(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x@(0, 1), x > 1.1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2e(cube(x));
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2f(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x@(0, 1), x < -0.1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2f(cube(x));
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2g(float x)
    case
    {
      x >= 1      -> requires Term ensures true;
      x <= 0.1    -> requires Term ensures true;
      0.1 < x < 1 -> requires Term[Seq{x@(0, 1), -0.1 < x < 1}] ensures true;
    }
{
  if ((0.1 < x) && (x < 1))
  {
    foo2g(cube(x));
  }
}
