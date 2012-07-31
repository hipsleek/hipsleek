/*
   ALGLIB - library for numerical analysis and data processing
   http://www.alglib.net/
*/ 

/* ------------------------------------------------
File: alglib-3.5.0.cpp/src/alglibinternal.cpp
Line 8558:
    // s > 0, mx > 0
    while(ae_fp_greater_eq(s*mx,1))
    {
        s = 0.5*s;
    }
*/

void loop1(float s, float mx)
  requires mx > 0 & s > 0 & Term[SeqDec{s, 0, s * mx < 1}] ensures true;
{
  if ( s * mx >= 1)
    loop1(s * 0.5, mx);
  else
    return;    
}




/* ------------------------------------------------
File: mpfr-3.1.1/src/set_d.c
Line 8562:
    // s > 0, mx > 0
    while(ae_fp_less(s*mx,0.5))
    {
        s = 2*s;
    }
*/

void loop2(float s, float mx)
  requires mx > 0 & s > 0 & Term[SeqDec{-s, -infinity, s * mx > 0.5}] ensures true;
{
  if ( s * mx <= 0.5)
    loop2(s * 2, mx);
  else
    return;    
}

