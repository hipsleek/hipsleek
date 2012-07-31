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

float abs(float x)
  requires true & Term
  ensures res = __abs(x);


void loop1(float z)
  case
  {
    2.0 < z < 4.0 -> requires Term[SeqDec{-z, (-infinity, -2.0), -infinity, __abs(z) >= 4.0}] ensures true;
    -4.0 < z < -2.0 -> requires Term[SeqDec{-(z*z), (-infinity, -4.0), -infinity, __abs(z) >= 4.0}] ensures true;
    z = 2.0 | z = -2.0 -> requires Loop ensures false;
    -2.0 < z < 2.0 -> requires true ensures true; 
    z >= 4.0 -> requires Term ensures true;
    z <= -4.0 -> requires Term ensures true;
  }
//  requires Term[SeqDec{z, 0, s * mx < 1}] ensures true;
{
  if (abs(z) < 4.0)
    loop1(z * z - 2);
  else
    return;
}
/*
void loop_int(int z)
  case
  {
    -4 < z < 4 -> requires true ensures true;
    z >= 4 -> requires Term ensures true;
    z <= -4 -> requires Term ensures true;
  }
//  requires Term[SeqDec{z, 0, s * mx < 1}] ensures true;
{
  if ((z < 4) && (z > -4))
    loop_int(z * z - 2);
  else
    return;    
}
*/