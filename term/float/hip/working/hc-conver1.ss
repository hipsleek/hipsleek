// update function: x = 2 - 1/x

void loop1(float x)
  case
  {
    x = 0.0 -> requires true ensures true;
    x != 0.0 -> requires Term[SeqCon(x, 1.0, x < 1.1)] ensures true;
  }
{
  if (x < 1.1)
    return;
  else
    loop1(2.0 - 1.0 / x);
}


// BUG
/*
void loop2(float x)
  case
  {
    x = 0.0 -> requires true ensures true;
    x != 0.0 -> requires Term[SeqCon(x, 1.0, x > -1)] ensures true;
  }
{
  if (x > -1)
    return;
  else
    loop2(2.0 - 1.0 / x);
}
*/

/*
void loop3(float x)
  requires x != 0.0 & Term[SeqCon(x, 1.0, x < -1)] ensures true;
{
  if (x < -1)
    return;
  else
    loop3(2.0 - 1.0 / x);
}

void loop4(float x)
  requires (x != 0.0) & Term[SeqCon(x, 1.0, x < -1)] ensures true;
{
  if (x  > 1)
    return;
  else
    loop4(2.0 - 1.0 / x);
}
*/

/*
void loop5(float x)
  requires (x != 0.0) ensures true;
{
  if (x  < 1)
    return;
  else
    loop5(2.0 - 1.0 / x);
}
*/


void loop6(float x)
  requires (x != 0.0) ensures true;
{
  if (x  > 1)
    return;
  else
    loop6(2.0 - 1.0 / x);
}
