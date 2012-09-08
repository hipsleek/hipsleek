//

// correct specs
void foo2a(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{2.0 * x@(0.0,+infty),x>0.1}, 1] ensures true;
  }
{
  if (x > 0.1)
    bar2a(x * 2.0);
}

void bar2a(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x@(0.0,+infty),x>0.1}, 0] ensures true;
  }
{
  if (x > 0.1)
    foo2a(x / 4.0);
}

// invalid specs
void foo2b(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{2.0 * x@(0.0,+infty),x>0.1}, 0] ensures true;
  }
{
  if (x > 0.1)
    bar2b(x * 2.0);
}

void bar2b(float x)
  case {
    x <= 0.1 -> requires Term ensures true;
    x > 0.1  -> requires Term[Seq{x@(0.0,+infty),x>0.1}, 1] ensures true;
  }
{
  if (x > 0.1)
    foo2b(x / 4.0);
}
