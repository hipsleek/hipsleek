float sin(float x)
  ensures res = sin(x);

float cos(float x)
  ensures res = cos(x);

float arcsin(float x)
  ensures res = arcsin(x);

float arccos(float x)
  ensures res = arccos(x);

float pow(float x, float y)
  ensures res = pow(x,y);

float pow_int(float x, int y)
  ensures res = pow(x,y);

float foo(float x)
  ensures res = x;
{
  return sin(arcsin(x)); 
}

float foo2(float x)
  ensures res = x;
{
  return cos(arccos(x));
}

float foo3(float x)
  ensures res = x;
{
  return arcsin(sin(x));
}

float foo4(float x)
  ensures res = x;
{
  return arccos(cos(x));
}