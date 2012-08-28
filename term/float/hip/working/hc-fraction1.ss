// update function: x = 2 - 1/x
/*
void loop1(float x)
  case
  {
    x = 0.0 -> requires true ensures true;
    x != 0.0 -> requires Term[SeqGen{x, 1.0, x < 1.1}] ensures true;
  }
{
  if (x < 1.1)
    return;
  else
    loop1(2.0 - 1.0 / x);
}
*/

// BUG

void loop2(float x)
  case
  {
    x = 0.0 -> requires Term ensures true;
    x = 1.0 -> requires Loop ensures false;
    x > 1.0 -> requires Term[SeqDec{x, (1.0, +infinity), x > -1.0}] ensures true;
    0 < x < 1.0 -> requires true ensures true;               // cannot write specs for Termination at this case
    -1 <= x < 0.0 -> requires Term ensures true;
    x <  -1 -> requires Term ensures true;
  }
{
  if (x < -1.0)
    return;
  else if (x != 0.0)
    loop2(2.0 - 1.0 / x);
}

void div2(float x)
  case
  {
    x = 0.0 -> requires Term ensures true;
    x > 2.0 -> requires Term[SeqGen{x, (0.0, +infinity), 0.0, x > 1.0}] ensures true;
    2.0 >= x > 0.0 -> requires true ensures true;            // cannot write specs for Termination at this case
    x < 0.0 -> requires Term ensures true;
  }
{
  if (x > 1.0)
    div2(x/2.0);
}


void loop3(float x)
  requires x != 0.0 & x!= 0.5 & Term[SeqGen{x, (-infinity, +infinity), 1.0, x < -1}] ensures true;
{
  if (x < -1)
    return;
  else
    loop3(2.0 - 1.0 / x);
}
/*
void loop4(float x)
  requires (x != 0.0) & Term[SeqGen{x, (-infinity, +infinity), 1.0, x < -1}] ensures true;
{
  if (x  > 1)
    return;
  else
    loop4(2.0 - 1.0 / x);
}
*/
void loop5(float x)
  requires (x != 0.0) ensures true;
{
  if (x  < 1)
    return;
  else
    loop5(2.0 - 1.0 / x);
}

void loop6(float x)
  requires (x != 0.0) ensures true;
{
  if (x  > 1)
    return;
  else if ((2.0 - 1.0/x) != 0.0)
    loop6(2.0 - 1.0 / x);
}
