float foo(float y)
  requires (1.0 < y & y < 1.1)
  ensures (exists x: x + 1.0 > 1.0 & x * x < 6.0  & 1/x < res);
{
  float a = 1.0;
//  assume (y >= 1.0) & (y < 1.1);
  float r = y * y  + y * y + y;
  return r;
}
/*

float bar(float y)
  requires (1.0 < y & y < 1.1)
  ensures (exists x: x + 1.0 > 1.0 & x * x < 6.0  & 1/x < res - 4);
{
  float a = 1.0;
//  assume (y >= 1.0) & (y < 1.1);
  float r = y * y + y * y + y;
  return r;
}
*/
