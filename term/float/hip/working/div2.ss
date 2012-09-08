/* sqrt examples */

float div2(float x)
  requires Term[] ensures res = x / 2.0;
{
  return x / 2.0;
}  

// correct specs
void foo2a (float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(0,+infty), 0.1}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2a(f);
  }
}

// correct specs
void foo2b (float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(0,+infty), x < -0.1}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2b(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo2c (float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(0.01,+infty), x < -0.1}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2c(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo2d (float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(-infty,+infty), x < -0.1}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2d(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo2e (float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(0.01,100), x < -0.1}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2e(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2f(float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(0.01,+infty), x > -0.1}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2f(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2g (float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(0.01,+infty), x < 0.1}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2g(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2h (float x)
  case
  {
    x >= -0.1  -> requires Term[] ensures true;
    x < -0.1   -> requires Term[Seq{-x@(0.01,+infty), x < -0.01}] ensures true;
  }
{
  if (x < -0.1)
  {
    float f = div2(x); 
    foo2h(f);
  }
}

