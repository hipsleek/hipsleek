/* sqrt examples */

float sqrt(float x)
  requires x >= 0 & Term[]
  ensures res = __sqrt(x);

// Correct specs
void foo2a (float x)
  case
  {
    x > 0.9       ->  requires Term[] ensures true;
    0 < x <= 0.9  ->  requires Term[Seq{-x, (-1.0, 0), -0.9}] ensures true;
    x = 0         ->  requires Loop ensures false;
    x < 0         ->  requires Term[] ensures true;    
  }
{
  if ((x >= 0) && (x <= 0.9))
  {
    float f = sqrt(x);
    foo2a(f);
  }
}

// Correct specs
void foo2b (float x)
  case
  {
    x > 0.9       ->  requires Term[] ensures true;
    0 < x <= 0.9  ->  requires Term[Seq{-x, (-1.0, 0), 0 <= x <= 0.9}] ensures true;
    x = 0         ->  requires Loop ensures false;
    x < 0         ->  requires Term[] ensures true;    
  }
{
  if ((x >= 0) && (x <= 0.9))
  {
    float f = sqrt(x);
    foo2b(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo2c (float x)
  case
  {
    x > 0.9       ->  requires Term[] ensures true;
    0 < x <= 0.9  ->  requires Term[Seq{-x, (-infty, 0), 0 <= x <= 0.9}] ensures true;
    x = 0         ->  requires Loop ensures false;
    x < 0         ->  requires Term[] ensures true;    
  }
{
  if ((x >= 0) && (x <= 0.9))
  {
    float f = sqrt(x);
    foo2c(f);
  }
}

// INVALID SPECS: inappropriate domain
void foo2d (float x)
  case
  {
    x > 0.9       ->  requires Term[] ensures true;
    0 < x <= 0.9  ->  requires Term[Seq{-x, (-1.0, 1), 0 <= x <= 0.9}] ensures true;
    x = 0         ->  requires Loop ensures false;
    x < 0         ->  requires Term[] ensures true;    
  }
{
  if ((x >= 0) && (x <= 0.9))
  {
    float f = sqrt(x);
    foo2d(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2e (float x)
  case
  {
    x > 0.9       ->  requires Term[] ensures true;
    0 < x <= 0.9  ->  requires Term[Seq{-x, (-1.0, 1), 0 <= x <= 1.0}] ensures true;
    x = 0         ->  requires Loop ensures false;
    x < 0         ->  requires Term[] ensures true;    
  }
{
  if ((x >= 0) && (x <= 0.9))
  {
    float f = sqrt(x);
    foo2e(f);
  }
}

// INVALID SPECS: inappropriate loop condition
void foo2f (float x)
  case
  {
    x > 0.9       ->  requires Term[] ensures true;
    0 < x <= 0.9  ->  requires Term[Seq{-x, (-1.0, 1), x > 0.9}] ensures true;
    x = 0         ->  requires Loop ensures false;
    x < 0         ->  requires Term[] ensures true;    
  }
{
  if ((x >= 0) && (x <= 0.9))
  {
    float f = sqrt(x);
    foo2f(f);
  }
}
