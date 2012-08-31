// fraction: f(x) = 1.0 + 2.0/x
/*
float abs(float x)
  requires Term
  ensures res = __abs(x);


// no using abs
void loop1(float x)
  case {
    x > 2.01          -> requires Term[Seq{x-2.0, (0, +infty), (x>2.01 | x<1.99) & x>0.0}] ensures true;
    1.99 <= x <= 2.01 -> requires Term ensures true;
    1.0 < x < 1.99    -> requires Term[Seq{2.0-x, (0, +infty), (x>2.01 | x<1.99) & x>0.0}] ensures true;
    0.0 < x <= 1.0    -> requires Term[Seq{(2.0-x)*2.0/x, (0, +infty), (x>2.01 | x<1.99) & x>0.0}] ensures true;
    x <= 0.0          -> requires Term ensures true;
  }
{
  if (((x>2.01) || (x<1.99)) && (x > 0.0))
    loop1(1.0 + 2.0/x);
}
*/
/*
void loop1f(float x)
  case {
    x > 1.99     -> requires Term[Seq{x-2.0, (0, +infty)}] ensures true;
    x <= 1.99    -> requires Term ensures true;
  }
{
  if (x>1.99)
    loop1f(1.0 + 2.0/x);
}
*/

void tmploop1(float x)
  case {
    x <= -0.1 -> requires Term ensures true;
    0 > x > -0.1 -> requires Term[Seq{-x, (0, 0.1)}] ensures true;
    x = 0 -> requires Loop ensures false;
    x > 0 -> requires Term[Seq{x, (0, +infty)}] ensures true;
  }
{
  if (x > -0.1)
    tmploop1(x/2.0);
}

/*

// using abs
void loop2(float x)
  case {
    x > 2.01          -> requires Term[Seq{__abs(x-2.0), (0, +infty), __abs(x-2.0)>0.01 & x>0.0}] ensures true;
    1.99 <= x <= 2.01 -> requires Term ensures true;
    1.0 < x < 1.99    -> requires Term[Seq{__abs(x-2.0), (0, +infty), __abs(x-2.0)>0.01 & x>0.0}] ensures true;
    0.0 < x <= 1.0    -> requires Term[Seq{__abs((x-2.0)*2.0/x), (0, +infty), __abs(x-2.0)>0.01 & x>0.0}] ensures true;
    x <= 0.0          -> requires Term ensures true;
  }
{
  if ((abs(x-2.0) > 0.01) && (x > 0.0))
    loop2(1.0 + 2.0/x);
}
*/
