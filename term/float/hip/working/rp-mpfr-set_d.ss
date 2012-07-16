/*
   GNU MPFR - library for multiple-precision floating-point computations with correct rounding
   http://www.mpfr.org/
*/ 

/* ------------------------------------------------
File: mpfr-3.1.1/src/set_d.c
Line 94:
      // d > 0      
      while (d >= 32768.0)
      {
        d *= (1.0 / 65536.0);
        exp += 16;
      }
*/

void loop1(float d)
  case
  {
    d > 0   ->  requires Term[SeqConDec(d, 0, 32768)] ensures true;
    d <= 0  ->  requires Term[] ensures true;
  }
{
  if ( d >= 32768)
    loop1(d * 1 / 65536);
  else
    return;    
}




/* ------------------------------------------------
File: mpfr-3.1.1/src/set_d.c
Line 99:
      // d > 0
      while (d >= 1.0)
        {
          d *= 0.5;
          exp += 1;
        }
*/
void loop2(float d)
  case
  {
    d > 0   -> requires Term[SeqConDec(d, 0, 1)] ensures true;
    d <= 0  -> requires Term[] ensures true;
  }
{
  if ( d >= 1)
    loop2(d * 0.5);
  else
    return;
}




/* ------------------------------------------------
File: mpfr-3.1.1/src/set_d.c
Line 107:
      // d > 0
      while (d < (1.0 / 65536.0))
        {
          d *=  65536.0;
          exp -= 16;
        }
*/

void loop3(float d)
/*
  // this specs will causes bug
  case
  {
    d > 0.0   -> requires Term[SeqConDec(-d, -infinity, - 1.0 / 65536.0)] ensures true;
    d <= 0.0  -> requires true ensures true;
  }
*/
  case
  {
    d > 0.0   -> requires Term[SeqConDec(-d, -infinity, d > 1.0 / 65536.0)] ensures true;
    d <= 0.0  -> requires true ensures true;
  }
{
  if ( d < 1.0 / 65536.0)
    loop3(d * 65536.0);
  else
    return;
}




/* ------------------------------------------------
File: mpfr-3.1.1/src/set_d.c
Line 107:
      // d > 0
      while (d < 0.5)
        {
          d *= 2.0;
          exp -= 1;
        }
*/

void loop4(float d)
/*
  // this spec will causes bug
  case
  {
    d > 0   -> requires Term[SeqConDec(-d, -infinity, -0.5)] ensures true;
    d <= 0  -> requires true ensures true;
  }
*/
  case
  {
    d > 0   -> requires Term[SeqConDec(-d, -infinity, d > 0.5)] ensures true;
    d <= 0  -> requires true ensures true;
  }
{
  if ( d < 0.5 )
    loop4(d * 2);
  else
    return;
}

