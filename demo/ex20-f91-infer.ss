
int f91(int n)

  infer[@post_n] 
  requires true
  ensures true;
/*
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;
 }
*/
{
  //dprint;
  if (91<=n) return n;
  else return f91(f91(n+1));
}

