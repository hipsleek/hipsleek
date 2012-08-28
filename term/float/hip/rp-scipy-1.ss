// BUG

/*
  File: scipy-0.11.0b1/scipy/special/cephes/ellie.c
*/


/********************
  Line 106:
      a = 1.0 - m;
      b = sqrt(a);
      c = sqrt(m);
      a = 1.0;
      d = 1;
      e = 0.0;
      mod = 0;

      while( fabs(c/a) > MACHEP )
      {
	      temp = b/a;
	      lphi = lphi + atan(t*temp) + mod * PI;
	      mod = (lphi + PIO2)/PI;
	      t = t * ( 1.0 + temp )/( 1.0 - temp * t * t );
	      c = ( a - b )/2.0;
	      temp = sqrt( a * b );
	      a = ( a + b )/2.0;
	      b = temp;
	      d += d;
	      e += c * sin(lphi);
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

global float c;
// a > 0, b > 0, machep > 0
void loop1 (float a, float b, float machep)
  case
  {
    a < 0.0 | b < 0.0 | machep < 0.0     ->   requires Term[] ensures true;
    !(a < 0.0 | b < 0.0 | machep < 0.0)  ->   requires Term[SeqDec{(a-b)/(2.0 * a), 0.0, machep}]
                                                ensures true;
  }
{
  if ((a < 0.0) || (b < 0.0) || (machep < 0.0))
    return;

  float c = (a - b) / 2.0;
  if (fabs(c/a) > machep)
  {
    float a1 = (a + b) / 2.0;
    float b1 *= 1.0;
    //b1 = sqrt(a);
    loop1(a1, b, machep);
  }
  
  return;
}


// Use constraint in Term specs

