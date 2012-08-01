/* sqrt examples */

float sqrt(float x)
  requires x >= 0 & Term
  ensures res = __sqrt(x);      // __sqrt(x) is the built-in function

// correct
void foo_term1(float x)
    case
    {
      x <= 1 -> requires Term ensures true;
      x > 1  -> requires Term[SeqDec{x, (1.0, +infinity), 1.0, 1.1}] ensures true;
    }
{
  if (x > 1.1)
  {
    foo_term1(sqrt(x));
  }
}

// bug in specs
void foo_term1a(float x)
    case
    {
      x <= 2.0 -> requires Term ensures true;
      x > 2.0  -> requires Term[SeqDec{x, (1.0, +infinity), 1.0, 1.1}] ensures true;
    }
{
  if (x > 1.1)
  {
    foo_term1a(sqrt(x));
  }
}

/*
void foo_term1b(int xxx)
    case
    {
      xxx <= 1 -> requires Term ensures true;
      xxx > 1  -> requires Term[xxx] ensures true;
    }
{
  if (xxx > 1)
  {
    foo_term1b(xxx-1);
  }
}
*/

// correct
void foo_term2(float x)
    case
    {
      x <= 0 -> requires Term ensures true;
      x > 0  -> requires Term[SeqDec{-x, (-1.0, 0.0), -1.0, -0.9}] ensures true;
    }
{
  if ((x > 0) && (x < 0.9))
  {
    foo_term2(sqrt(x));
  }
}

// correct
void foo_term3(float x)
    case
    {
      x <= 0 -> requires Term ensures true;
      x > 0  -> requires Term[SeqGen{x, (0.0, 1.0), 1.0, !((x < 0.9) | (x > 1.1))}] ensures true;
    }
{
  if (x > 0)
  {
    if ((x < 0.9) || (x > 1.1))
    {
      foo_term3(sqrt(x));
    }
  }
}

// correct
void foo_loop(float x)
    case
    {
      x <= 0.1 -> requires Term ensures true;
      x > 0.1  -> requires Loop ensures false;
    }
{
  if (x > 0.1)
  {
    foo_loop(sqrt(x));
  }
}

// false specs
void foo_term4(float x)
    case
    {
      x <= 0 -> requires Term ensures true;
      x > 0  -> requires Term[SeqGen{x, (-1.0, 0.0), -1.0, x > 0}] ensures true;        // limit  = 1.0, not -1.0
    }
{
  if (x > 0)
  {
    if ((x < 0.9) || (x > 1.1))
    {
      foo_term4(sqrt(x));
    }
  }
}

// false specs
void foo_term5(float x)
    case
    {
      x <= 0 -> requires Term ensures true;
      x > 0  -> requires Term[SeqGen{x, (0.0, 1.0), 1.0, x < 0}] ensures true;        // invalid bound
    }
{
  if (x > 0)
  {
    if ((x < 0.9) || (x > 1.1))
    {
      foo_term5(sqrt(x));
    }
  }
}

// false specs
void foo_term6(float x)
    case
    {
      x <= 0 -> requires Term ensures true;
      x > 0  -> requires Term[SeqGen{x, (0.0, 1.0), 1.0, x < 0}] ensures true;
    }
{
  foo_term6(sqrt(x));
}
