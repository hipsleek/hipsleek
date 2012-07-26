/*
   GLIBC - the GNU C Library
   http://www.gnu.org/software/libc/
*/ 

/* ------------------------------------------------
File: glibc-2.16.0/nptl/sockperf.c
    complex double z = c.z;
    while (cabs (z) < 4.0)
	  {
	    z = z * z - 1;
	    if (++rnds == 255)
	      break;
	  }
*/

float abs(float x)
{
  if (x > 0)
    return x;
  else
    return -x;
}


// TRUNG: BUG with sqrt --> uninterpreted function
void loop1(float z)
  case
  {
    z < (1 - sqrt(5))/2 -> requires Term[SeqDec(z, -infinity, -4 )] ensures true;
    z >= (1 - sqrt(5))/2 -> requires false ensures true;
  }

//  requires Term[SeqDec(z, 0, s * mx < 1)] ensures true;
{
  if (abs(z) < 4.0)
    loop1(z * z - 1);
  else
    return;    
}
