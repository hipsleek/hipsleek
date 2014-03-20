float sin(float x)
  ensures res = sin(x);

float cos(float x)
  ensures res = cos(x);

float pow(float x, float y)
  ensures res = pow(x,y);

float pow_int(float x, int y)
  ensures res = pow(x,y);

// passed
float pythagoras1(float x)
  ensures  res = 1.0;
{
  float y = sin(x) * sin(x) + cos(x) * cos(x);
  return y;
}


// failed when testing with mathematica
// one of the reason maybe that the Resolve of mathematica
// is unable to eliminate quantifiers from the system 
// with inexact coefficients (pow(x, 2.0))
float pythagoras2(float x)
  ensures  res = 1.0;
{
  float y = pow(sin(x), 2.0) + pow(cos(x), 2.0);
  return y;
}


// passed
float pythagoras3(float x)
  ensures  res = 1.0;
{
  float y = pow_int(sin(x), 2) + pow_int(cos(x), 2);
  return y;
}
