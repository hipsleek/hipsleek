// int modulo(int x, int y)
//     requires x >= 0 & y > 0 ensures exists r: res = x - r * y & 0 <= res < y & r >= 0;
// {
//   if (x < y) return x;
//   else return modulo(x - y, y);
// }

int modulo(int x)
    requires x >= 0
    ensures exists r: res = x - r * 10 & 0 <= res < 10 & r >= 0;
{
  if (x < 10) return x + 2;
  else return modulo(x - 10);
}