// fraction: f(x) = 1 + 2/x

/*
void loop1(float x)
  case {
    x <= 3 -> requires Term ensures true;
    x > 3  -> requires Term[SeqDec{__abs(x-2.0), (0.0, +infinity), x>3}] ensures true;
  }
{
  if (x>3)
    loop1(1+2/x);
}
*/
/*
void loop1b(float x)
  case {
    x <= 3 -> requires Term ensures true;
    x > 3  -> requires Term[SeqDec{__abs(x-1.0), [0.0, +infinity), x>3.0}] ensures true;
  }
{
  if (x>3)
    loop1b(1+2/x);
}

void loop1b1(float x)
  case {
    x <= 3 -> requires Term ensures true;
    x > 3  -> requires Term[SeqDec{__abs(x-2.0), [0.0, +infinity), x>3.0}] ensures true;
  }
{
  if (x>3)
    loop1b1(1+x/2);
}
*/
void loop1c(float x)
  case {
    !((x>2.1) | (1.0<x<1.9)) -> requires Term ensures true;
    ((x>2.1)  | (1.0<x<1.9)) -> requires Term[SeqDec{__abs(x-2.0), (0.0, +infinity), ((x>2.1) | (x<1.9))}] ensures true;
  }
{
  if (((x>2.1) || ((x>1.0) && (x<1.9))) && (x != 0.0))
    loop1c(1+2/x);
}
