// Change each of the MayLoop below to
// either (i) Term[..] or (ii) Loop, so that 
// termination or non-termination property for 
// gcd function is completely proven.

int gcd(int m, int n)
case {
 m=n -> requires MayLoop ensures res=m;
 m!=n ->
  case {
    m <= 0 -> requires MayLoop ensures false;
    m > 0 -> 
    case {
	  n <= 0 -> requires MayLoop ensures false;
	  n > 0 -> requires MayLoop ensures res>0;
	}
  }
}
{
   if (m == n) return m;
   else if (m > n) return gcd(m-n, n);
   else return gcd(m, n-m);
}
