int mc91(int n)
infer[@term_wo_post] 
//requires true ensures true;
//requires true ensures res>=91;
requires true ensures n>=101 & res=n-10 | n<101 & res=91;
{
  if (n > 100) return n-10;
  else return mc91(mc91(n+11));
}
