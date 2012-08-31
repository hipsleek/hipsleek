// SUCCESS

/*
  File: scipy-0.11.0b1/scipy/special/cephes/incbet.c
*/


/********************
    Line 364:        
      
      ai = 1.0 / a;
      u = (1.0 - b) * x;
      v = u / (a + 1.0);
      t1 = v;
      t = u;
      n = 2.0;
      s = 0.0;
      z = MACHEP * ai;
      while( fabs(v) > z )
	      {
	      u = (n - b) * x / n;
	      t *= u;
	      v = t / (a + n);
	      s += v; 
	      n += 1.0;
	      }
*/

// 
void loop1 (float u, float t, float n, float b, float x, float a)
  case
  {
    ((u <= 0) | (t <= 0) | (b >=1) | (b <= 0) | (x <= 0) | (a <= 0) | (n <= 1)) -> 
        requires Term[] ensures true;
    !((u <= 0) | (t <= 0) | (b >=1) | (b <= 0) | (x <= 0) | (a <= 0) | (n <= 1)) -> 
        requires Term[Seq{-(t/(a+n)), -infty, t/(a+n) < 0.1}] ensures true;
  }
{
  if ((u <= 0) || (t <= 0) || (b >=1) || (b <= 0) || (x <= 0) || (a <= 0) || (n <= 1))
    return;
  float u1 = (n - b) * x * n;
  float t1 = t * u;
  float n1 = n + 1;
  if (t1 / (a + n)  > 0.1)
    loop1(u1, t1, n1, b, x, a);
  return;
}


