// UNSURE

/*
  File: scipy-0.11.0b1/scipy/special/cephes/airy.c
*/


/********************
  Line 500:
        pkm2 = 0.0;
        qkm2 = 1.0;
        pkm1 = x;
        qkm1 = *n + *n;
        xk = -x * x;
        yk = qkm1;
        ans = 0.0; // ans=0.0 ensures that t=1.0 in the first iteration 
        ctr = 0;
        do {
	        yk += 2.0;
	        pk = pkm1 * yk + pkm2 * xk;
	        qk = qkm1 * yk + qkm2 * xk;
	        pkm2 = pkm1;
	        pkm1 = pk;
	        qkm2 = qkm1;
	        qkm1 = qk;

	        // check convergence
	        if (qk != 0 && ctr > miniter)
	            r = pk / qk;
	        else
	            r = 0.0;

	        if (r != 0) {
	            t = fabs((ans - r) / r);
	            ans = r;
	        } else {
	            t = 1.0;
	        }

	        if (++ctr > maxiter) {
	            mtherr("jv", UNDERFLOW);
	            goto done;
	        }
	        if (t < MACHEP)
	            goto done;

	        // renormalize coefficients
	        if (fabs(pk) > big) {
	            pkm2 /= big;
	            pkm1 /= big;
	            qkm2 /= big;
	            qkm1 /= big;
	        }
        }
        while (t > MACHEP);
*/

float fabs (float x)
  requires false ensures true;
{
  if (x >= 0.0)
    return x;
  else
    return (0.0 - x);
}

// k > 0, f = 1.0, uf > 0, z > 0
void loop1 (float uf, float f, float k, float z)
{

  return;
}


