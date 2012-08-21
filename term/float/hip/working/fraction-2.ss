// fraction: f(x) = 1.5 + 1.0/x
/*
float abs(float x)
  requires Term
  ensures res = __abs(x);
*/
/*
void loop1(float x)
  case {
    x <= 2.1 -> requires Term ensures true;
    x > 2.1  -> requires Term[SeqDec{__abs(x-2.0), (0, +infinity), x > 2.1}] ensures true;
  }
{
  if (x > 2.1)
    loop1(1.5 + 1.0/x);
}
*/

/*
void loop2(float x)
  case {
    x <= 0.5 -> requires Term ensures true;
    1.1 <= x <= 2.1 -> requires Term ensures true;
    0.5 < x < 1.1 | x > 2.1 -> requires Term[SeqDe{__abs(x-2.0), (0, +infinity), (x<1.1 | x > 2.1)}] ensures true;
  }
{
  if (((0.5 < x) && (x < 1.1)) || (x > 2.1))
    loop2(1.5 + 1.0/x);
}
*/

void loop3(float x)
  case {
    x > 2.1 -> requires Term[SeqDec{x-2.0, (0, +infinity), x-2.0 > 0.1}] ensures true;
    1.9 <= x <= 2.1 -> requires Term ensures true;
    0.5 < x < 1.9 -> requires Term[SeqDec{2.0-x, (0, +infinity), 2.0-x > 0.1}] ensures true;
//    0 < x <= 0.5 -> requires true ensures true;
    0 < x <= 0.5 -> requires Term[SeqDec{(2.0-x)/x, (0, +infinity), (2.0-x) > 0.1}] ensures true;
    x = 0.0 -> requires Term ensures true;
    -0.5 <= x < 0 -> requires true ensures true;
//    -0.5 <= x < 0 -> requires Term[SeqDec{__abs((x-2.0)/x), (0, +infinity), __abs(x-2.0) > 0.1}] ensures true;
    x < -0.5 -> requires true ensures true;
//    x < -0.5 -> requires Term[SeqDec{__abs(x-2.0), (0, +infinity), __abs(x-2.0) > 0.1}] ensures true;
  }
{
  if (((x > 2.1) || (x<1.9)) && (x != 0.0))
    loop3(1.5 + 1.0/x);
}


