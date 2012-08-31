//

// correct specs
void foo1a(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x,(0.0,+infty),x>0.1}, 1] ensures true;
  }
{
  if (x > 0.1)
    bar1a(x);
}

void bar1a(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x,(0.0,+infty),x>0.1}, 0] ensures true;
  }
{
  if (x > 0.1)
    foo1a(x/2.0);
}

// invalid specs
void foo1b(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x,(0.0,+infty),x>0.1}, 0] ensures true;
  }
{
  if (x > 0.1)
    bar1b(x);
}

void bar1b(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x,(0.0,+infty),x>0.1}, 1] ensures true;
  }
{
  if (x > 0.1)
    foo1b(x/2.0);
}
