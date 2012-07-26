// BUG in parser (float = float)

/*
  File: scipy-0.11.0b1/scipy/special/cephes/airy.c
*/


/********************
  Line 397:
    double t, u, y, z, k;
    int ex;

    z = -x * x / 4.0;
    u = 1.0;
    y = u;
    k = 1.0;
    t = 1.0;

    while (t > MACHEP) {
	    u *= z / (k * (n + k));
	    y += u;
	    k += 1.0;
	    if (y != 0)
	        t = fabs(u / y);
    }
*/

float fabs (float x)
  requires false ensures true;
{
  if (x >= 0.0)
    return x;
  else
    return (0.0 - x);
}

// z < 0, k > 0
// n > 0
void loop1 (float u, float y, float k, float n, float z, float t)
  case
  {
    (z >= 0.0 | k <= 0.0 | n <= 0.0 | t <= 0.0 | (y >= 0.0 & y <= 0.0))    ->  requires Term[] ensures true;
    !(z >= 0.0 | k <= 0.0 | n <= 0.0 | t <= 0.0 | (y >= 0.0 & y <= 0.0))   ->  requires Term[SeqDec(t, 0.0, 0.1)] ensures true;    
  }
{
  if ((z >= 0.0) || (k <= 0.0) || (n <= 0.0) || (t <= 0.0) || ((y >= 0.0) && (y <= 0.0)))
    return;
  
  float u1 = u * z / (k * (n + k));
  float y1 = y + u1;
  float k1 = k + 1.0;

  float t1 = t;
  if (y != 0.0)
    t1 = fabs(u/y);

  if( t1 < 0.1)
    return;
    
  loop1(u1,y1,k1,n, z, t1);
  return;
}


