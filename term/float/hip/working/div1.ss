/* sqrt examples */

float div2(float x)
  requires Term[] ensures res = x / 2.0;
{
  return x / 2.0;
}  

// correct specs
void foo1a (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (0,+infty), 0.1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1a(f);
  }
}

// correct specs
void foo1b (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (0,+infty), x > 0.1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1b(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo1c (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (0.01,+infty), x > 0.1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1c(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo1d (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (-infty,+infty), x > 0.1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1d(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo1e (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (0,100), x > 0.1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1e(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo1f (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (0,+infty), x < 0.1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1f(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo1g (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (0,+infty), x > -0.1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1g(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo1h (float x)
  case
  {
    x <= 0.1  -> requires Term[] ensures true;
    x > 0.1   -> requires Term[Seq{x @ (0,+infty), x < 1}] ensures true;
  }
{
  if (x > 0.1)
  {
    float f = div2(x); 
    foo1h(f);
  }
}

