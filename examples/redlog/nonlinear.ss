bool is_triangle(float a, float b, float c)
  requires a > 0 & b > 0 & c > 0
  ensures res & a+b>c & a+c>b & b+c>a or !res & (a+b<=c | a+c<=b | b+c<=a);
{
  if ((a+b)*(a+b) > c*c && (a-b)*(a-b) < c*c) return true;
  return false;
}
