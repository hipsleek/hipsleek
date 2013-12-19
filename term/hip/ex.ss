/*while (x > 0)
  requires Term[x, y]
  ensures true;
{ x = x - 1;
  y = 2*y; }
*/

void foo(ref int x, ref int y)
  requires Term[x,y] & y>=0
  ensures true;
{
  if (x>0) {
    x=x-1;
    y=2*y;
    foo(x,y);
  }
}
