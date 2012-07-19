float time(float t)
  requires t > 0.0
  ensures res > t;
{

}

float falling(float h, float v, float t, float g)
  requires h > 0.0 & v > 0.0 & t > 0.0 & g > 0.0
  ensures (exists t: h - v * t = 0.0);
{
  if (h >= 0)
  {
    float h1 = h - v * t;
    float v1 = v - g * t;
    t = time(t);
    return falling(h1, v1, t, g);
  }
  else
    return h;
}

/*
void bounce(float h, float t)
{
  if (h == 0)
  {
    v = -c * v;
  }
}
*/
