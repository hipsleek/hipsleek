/* sqrt examples */

float sqrt(float x)
  requires x >= 0 & Term[]
  ensures res = __sqrt(x);

// Correct specs
void foo1a (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (1.0, +infty), 1.1}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1a(f);
  }
}

// Correct specs
void foo1b (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (1.0, +infty), x > 1.1}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1b(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo1c (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (0.0, +infty), x > 1.1}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1c(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo1d (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (1.0, 1000.0), x > 1.1}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1d(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo1e (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (1.0, +infty), x > 0.1}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1e(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo1f (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (1.0, +infty), x < 1.1}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1f(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo1g (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (1.0, +infty), x > 1}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1g(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo1h (float x)
  case
  {
    x <= 1.1  -> requires Term[] ensures true;
    x > 1.1   -> requires Term[Seq{x, (1.0, +infty), x >= 1.0}] ensures true;
  }
{
  if (x > 1.1)
  {
    float f = sqrt(x);
    foo1h(f);
  }
}

