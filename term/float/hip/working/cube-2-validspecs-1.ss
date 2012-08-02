/*
  cube examples 
*/

//---- hip ----

float cube(float x)
  requires Term
  ensures res = __pow(x,3);      // __pow(x) is the built-in function



/*void foo1b(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 < x < 1 -> requires Term[SeqDec{x, (-0.0, 1.0), -0.0, 0.1}] ensures true;
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo1b(cube(x));
  }
}
*/
void foo1(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 <= x < 1 -> requires Term[SeqDec{x, (-0.0, 1.0), -0.0, x < 0.1}] ensures true;
      x < 0.1    -> requires Term ensures true;
    }
{
  if (x >= 0.1)
  {
    foo1(cube(x));
  }
}

void foo1b(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 <= x < 1 -> requires Term[SeqDec{x, (-0.0, 1.0), -0.0, x >=0.1}] ensures true;
      x < 0.1    -> requires Term ensures true;
    }
{
  if (x >= 0.1)
  {
    foo1b(cube(x));
  }
}

void foo2(float x)
    case
    {
      x >= 1.0      -> requires Loop ensures false;
      0.1 <= x < 1 -> requires Term[SeqDec{x, (-0.0, 1.0), -0.0, 0.1}] ensures true;
      x < 0.1    -> requires Term ensures true;
    }
{
  if (x >= 0.1)
  {
    foo1(cube(x));
  }
}

/*

void foo2(float x)
    case
    {
      x >= 1      -> requires Loop ensures false;
      0.1 < x < 1 -> requires Term[SeqDec{x, (0.0, 1.0), 0.0, x<=0.1}] ensures true;
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo2(cube(x));
  }
}


void foo3(float x)
    case
    {
      x >= 1      -> requires Loop ensures false;
      0.0 <= x < 1 -> requires Loop ensures false;
      x < 0.0    -> requires Term ensures true;
    }
{
  if (x >= 0.0)
  {
    foo3(cube(x));
  }
}
*/
/*
void foo2(float x)
    case
    {
      x >= 1      -> requires Loop ensures false;
      0.1 < x < 1 -> requires Term[SeqDec{x, (0.0, 1.0), 0.0, x <= 0.1}] ensures true;
      x <= 0.1    -> requires Term ensures true;
    }
{
  if (x > 0.1)
  {
    foo2(cube(x));
  }
}
*/
