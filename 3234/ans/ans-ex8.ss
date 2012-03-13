int gcd(int m, int n)// do all cases terminate? try and annotate and verify the termination 
case {
 m=n -> requires Term ensures res=m;
 m!=n ->
  case {
    m <= 0 -> requires Loop ensures false;
    m > 0 -> 
    case {
	  n <= 0 -> requires Loop ensures false;
	  n > 0 -> requires Term[n+m] ensures res>0;
	}
  }
}
{
   if (m == n) return m;
   else if (m > n) return gcd(m-n, n);
   else return gcd(m, n-m);
}
