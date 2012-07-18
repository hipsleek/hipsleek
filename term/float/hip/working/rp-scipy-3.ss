/*
  File: scipy-0.11.0b1/scipy/special/cephes/airy.c
*/


/********************
  Line 500:
      f = 1.0;
      g = x;
      t = 1.0;
      uf = 1.0;
      ug = x;
      k = 1.0;
      z = x * x * x;
      while( t > MACHEP )
      {
	      uf *= z;
	      k += 1.0;
	      uf /=k;
	      ug *= z;
	      k += 1.0;
	      ug /=k;
	      uf /=k;
	      f += uf;
	      k += 1.0;
	      ug /=k;
	      g += ug;
	      t = fabs(uf/f);
      }
*/

// k >= 1.0, f >= 1.0, uf > 0, z > 0
void loop1 (float uf, float f, float k, float z)
  case
  {
    (uf <= 0.0 | f < 1.0 | k <= 1.0 | z <= 0.0) -> requires Term[] ensures true;
    !(uf <= 0.0 | f < 1.0 | k <= 1.0 | z <= 0.0) -> requires Term[SeqCon(uf/f, 1.0, uf/f < 0.1)] ensures true;
  }
{
  if ((uf <= 0.0) || (f < 1.0) || (k < 1.0) || (z <= 0.0)) 
    return;
    
  float uf1 = uf * z;
  float k1 = k + 1.0;
  float uf2 = uf1 / k1;
  float k2 = k1 + 1.0;
  float uf3 = uf2 / k2;
  float f1 = f + uf3;

  if (uf3/f1 > 0.1)
    loop1 (uf3, f1, k1, z);
 
  return;
}
