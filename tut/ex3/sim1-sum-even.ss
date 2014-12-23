int sumE(int n)

 case {
   exists (k: n>=0 & n=3*k) -> requires Term[n] ensures true;
   n < 0 | exists (k: n=3*k+1) -> requires Loop ensures false;
 }

{ if (n==0) return 0;
  else return n+sumE(n-2);
}

