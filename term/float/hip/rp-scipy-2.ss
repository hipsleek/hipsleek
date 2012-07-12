// BUG

/*
  File: scipy-0.11.0b1/scipy/special/cephes/ndtr.c
*/


/********************
  Line 500:
    double  log_LHS, a
            last_total = 0,
            right_hand_side = 1,
            numerator = 1,
            denom_factor = 1,
            denom_cons = 1.0/(a*a);
            long sign = 1, i = 0;
    if (a > -20 ) {
      return log(ndtr(a));
    }
    log_LHS = -0.5*a*a - log(-a) - 0.5*log(2*M_PI); 
    
    while (fabs(last_total - right_hand_side) > DBL_EPSILON) {
      i += 1;
      last_total = right_hand_side;
      sign = -sign;
      denom_factor *= denom_cons;
      numerator *= 2*i - 1; 
      right_hand_side += sign * numerator * denom_factor; 
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

void loop1 (float rhs, float last_total)
{
  
  return;
}


// Use constraint in Term specs

