/*
  cube examples 
*/

//---- hip ----

float cube(float x)
  requires Term
  ensures res = __pow(x,3);      // __pow(x) is the built-in function

void foo1(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[SeqDec{-x, (-infinity, -1), -1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1(cube(x));
  }
}

void foo2(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[SeqDec{-x, (-infinity, -1), x < 1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo2(cube(x));
  }
}

/*
void foo1(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[SeqDec{-x, (-infinity, -1), -1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo1(cube(x));
  }
}

void foo2(float x)
    case
    {
      x >= 1.1    -> requires Term ensures true;
      x <= 1      -> requires Loop ensures false;
      1 < x < 1.1 -> requires Term[SeqDec{-x, (-infinity, -1), x >= 1.1}] ensures true;
    }
{
  if (x < 1.1)
  {
    foo2(cube(x));
  }
}
*/
