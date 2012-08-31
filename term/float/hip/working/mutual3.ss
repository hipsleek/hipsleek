//

// correct specs
void foo3a(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{2.0 * x,(0.0,+infty),x>0.1}] ensures true;
  }
{
  if (x > 0.1)
    bar3a(x);
}

void bar3a(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x,(0.0,+infty),x>0.1}] ensures true;
  }
{
  if (x > 0.1)
    foo3a(x / 4.0);
}

// invalid specs
void foo3b(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{2.0 * x,(0.0,+infty),x>0.1}] ensures true;
  }
{
  if (x > 0.1)
    bar3b(x);
}

void bar3b(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x,(0.0,+infty),x>0.1}] ensures true;
  }
{
  if (x > 0.1)
    foo3b(x / 4.0);
}
