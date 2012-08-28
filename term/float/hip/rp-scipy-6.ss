// BUG in parser (float = float)

/*
  File: scipy-0.11.0b1/scipy/special/cephes/airy.c
*/


/********************
  Line 397:
    double t, u, z, k, sign, conv;
    double p, q, j, m, pp, qq;
    int flag;

    m = 4.0 * n * n;
    j = 1.0;
    z = 8.0 * x;
    k = 1.0;
    p = 1.0;
    u = (m - 1.0) / z;
    q = u;
    sign = 1.0;
    conv = 1.0;
    flag = 0;
    t = 1.0;
    pp = 1.0e38;
    qq = 1.0e38;

    while (t > MACHEP) {
	    k += 2.0;
	    j += 1.0;
	    sign = -sign;
	    u *= (m - k * k) / (j * z);
	    p += sign * u;
	    k += 2.0;
	    j += 1.0;
	    u *= (m - k * k) / (j * z);
	    q += sign * u;
	    t = fabs(u / p);
	    if (t < conv) {
	        conv = t;
	        qq = q;
	        pp = p;
	        flag = 1;
	    }
      //stop if the terms start getting larger
	    if ((flag != 0) && (t > conv)) {
        #if CEPHES_DEBUG
              printf("Hankel: convergence to %.4E\n", conv);
        #endif
              goto hank1;
	    }
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

// 
void loop1 (float k, float j, float u, float p, float sign, float t, float m, float z)
  requires false ensures true;
{
  if ((m < 1.0) || (k < 1.0) || (j < 1.0) || ((sign != -1.0) && (sign != 1.0)))
    return; 
  
  float k1 = k + 2.0;
  float j1 = j + 1.0;
  float u1 = (m - k1 * k1) / (j1 * z);
  float p1 = p + sign * u1;
  float k2 = k1 + 2.0;
  float j2 = j1 + 1.0;
  float u2 = (m - k2 * k2) / (j2 * z);
  float t1 = fabs(u2/p1);
  if (t1 > 0.1)
    loop1(k2, j2, u2, p1, sign, t1, m, z);
  
  return;
}


