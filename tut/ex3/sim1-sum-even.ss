int sumE(int n)
//infer [@term] 
//infer [@post_n]
  //requires true ensures true;
//requires true & (n=0 | exists(k: k>=0 & n=2*k)) & Term[n] ensures true;
case {
exists (k: n>=0 & n=2*k) -> requires Term[n] ensures true;
n < 0 | exists (k: n=2*k + 1) -> requires Loop ensures false;
}
/*
requires  true & (n<0 | exists(k:k>=0 & n!=2*k)) & Loop 
ensures false;
*/
/*
 case {
   (exists k: k>=0 & n=2*k) -> requires Term[n] ensures true;
   (exists k: n<0 | n!=2*k) -> requires Loop ensures false;
 }
*/
{ if (n==0) return 0;
  else return n+sumE(n-2);
}

