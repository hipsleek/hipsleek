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
  requires Term
  ensures res = __abs(x);


void loop1(float z)
  case
  {
    z >= 4  -> requires Term ensures true;
    (1 + __sqrt(5))/2 < z < 4 -> requires Term[Seq{-z, (-infinity, -(1+__sqrt(5))/2), __abs(z) >= 4 }] ensures true;
    z = (1 - __sqrt(5))/2 | z = (1+__sqrt(5))/2 -> requires Loop ensures false;
    (1-__sqrt(5))/2 < z < (1+__sqrt(5))/2 -> requires true ensures true; // TRUNG: do further analysis here
    -4 < z < (1 - __sqrt(5))/2 -> requires Term[Seq{-__abs(z), (-infinity, -(1+__sqrt(5))/2), __abs(z) >= 4 }] ensures true;
    z <= -4 -> requires Term ensures true;
  }
{
  if (abs(z) < 4.0)
    loop1(z * z - 1);
  else
    return;    
}
