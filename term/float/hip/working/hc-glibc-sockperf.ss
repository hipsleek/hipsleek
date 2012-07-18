// hand-crafted example base on sockpert.c file

/* ------------------------------------------------
Real program:

File: glibc-2.16.0/nptl/sockperf.c
    complex double z = c.z;
    while (cabs (z) < 4.0)
	  {
	    z = z * z - 1;
	    if (++rnds == 255)
	      break;
	  }
	  
	  
==> Hand-crafted program:
    while (cabs (z) < 4.0)
	  {
	    z = z * z - 2;
	    if (++rnds == 255)
	      break;
	  }
*/


void loop1(float z)
  case
  {
    -4 < z < 4 -> requires Loop[] ensures true;
    z >= 4 -> requires Term[SeqConDec(-z, -infinity, -4)] ensures true;
    z <= -4 -> requires Term[SeqConDec(-z, -infinity, -4)] ensures true;
  }

//  requires Term[SeqConDec(z, 0, s * mx < 1)] ensures true;
{
  if ((z < 4.0) && (z > -4.0))
    loop1(z * z - 2);
  else
    return;    
}
