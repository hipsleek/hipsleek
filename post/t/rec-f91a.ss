
// 90 -> 91
relation postA(int n, int r).
relation postB(int n, int r).

int f91(int n)
infer [postA,postB]
 case {
  n>=91 ->  ensures postA(n,res);
  n<91 -> ensures postB(n,res);
 }
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*
[RELDEFN postA: ( n=res & 91<=res) -->  postA(n,res),
RELDEFN postB: ( postA(v_int_17_1188,res) & 91<=v_int_17_1188 & n=90 & n'=90 & postA(1+
n',v_int_17_1188)) -->  postB(n,res),
RELDEFN postB: ( postB(v_int_17_1191,res) & v_int_17_1191<=90 & n=90 & n'=90 & postA(1+
n',v_int_17_1191)) -->  postB(n,res),
RELDEFN postB: ( postA(v_int_17_1194,res) & 91<=v_int_17_1194 & n<=89 & postB(1+
n,v_int_17_1194)) -->  postB(n,res),
RELDEFN postB: ( postB(v_int_17_1197,res) & v_int_17_1197<=90 & n<=89 & postB(1+
n,v_int_17_1197)) -->  postB(n,res)]
*/
