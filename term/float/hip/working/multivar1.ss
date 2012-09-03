float pow(float x, int n)
  requires Term[]
  ensures res = __pow(x,n);

void loop(float x, float y)
  case
  {
    y <= 0 -> requires Term[] ensures true;
    y > 0  -> requires Term[Seq{y-__pow(x,2); (}]
  }
{
  if ((y - pow(x,2)) > 100)
  {
    y = pow(y,10) + 1000;
    x--;
    loop(x,y);
  }
}
