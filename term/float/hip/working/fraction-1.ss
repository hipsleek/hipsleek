// fraction: f(x) = 1.0 + 2.0/x

float abs(float x)
  requires Term
  ensures res = __abs(x);


// no using abs
void loop1(float x)
  case {
    x > 2.01          -> requires Term[SeqDec{x-2.0, (0, +infinity), (x>2.01 | x<1.99) & x>0.0}] ensures true;
    1.99 <= x <= 2.01 -> requires Term ensures true;
    1.0 < x < 1.99    -> requires Term[SeqDec{2.0-x, (0, +infinity), (x>2.01 | x<1.99) & x>0.0}] ensures true;
    0.0 < x <= 1.0    -> requires Term[SeqDec{(2.0-x)*2.0/x, (0, +infinity), (x>2.01 | x<1.99) & x>0.0}] ensures true;
    x <= 0.0          -> requires Term ensures true;
  }
{
  if (((x>2.01) || (x<1.99)) && (x > 0.0))
    loop1(1.0 + 2.0/x);
}

/*

// using abs
void loop2(float x)
  case {
    x > 2.01          -> requires Term[SeqDec{__abs(x-2.0), (0, +infinity), __abs(x-2.0)>0.01 & x>0.0}] ensures true;
    1.99 <= x <= 2.01 -> requires Term ensures true;
    1.0 < x < 1.99    -> requires Term[SeqDec{__abs(x-2.0), (0, +infinity), __abs(x-2.0)>0.01 & x>0.0}] ensures true;
    0.0 < x <= 1.0    -> requires Term[SeqDec{__abs((x-2.0)*2.0/x), (0, +infinity), __abs(x-2.0)>0.01 & x>0.0}] ensures true;
    x <= 0.0          -> requires Term ensures true;
  }
{
  if ((abs(x-2.0) > 0.01) && (x > 0.0))
    loop2(1.0 + 2.0/x);
}
*/
