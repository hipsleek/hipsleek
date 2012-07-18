void loop(int x, int y)
  requires x > 3
  case {
    x < y -> requires Term[y-x] ensures true;
    x >= y -> requires Term[] ensures true;
  }
{
  if (x<y) {
    x = x*x*x -2*(x*x)-x+2;
    loop(x,y);
  }
}
