float sin(float x)
  ensures res = sin(x);

float cos(float x)
  ensures res = cos(x);

float pow(float x, float y)
  ensures res = pow(x,y);

float pythagoras1(float x)
  ensures  res = 1.0;
{
  float y = sin(x) * sin(x) + cos(x) * cos(x);
  return y;
}

float pythagoras2(float x)
  ensures  res = 1.0;
{
  float y = pow(sin(x), 2.0) + pow(cos(x), 2.0);
  return y;
}
