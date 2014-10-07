
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
RELDEFN postA: ( postA(v_int_15_1187,res) & 91<=v_int_15_1187 & n=90 & n'=90 & postA(1+
n',v_int_15_1187)) -->  postA(n,res),
RELDEFN postA: ( postA(v_int_15_1190,res) & v_int_15_1190<=90 & n=90 & n'=90 & postA(1+
n',v_int_15_1190)) -->  postA(n,res),
RELDEFN postA: ( postA(v_int_15_1193,res) & 91<=v_int_15_1193 & n<=89 & postA(1+
n,v_int_15_1193)) -->  postA(n,res),
RELDEFN postA: ( postA(v_int_15_1196,res) & v_int_15_1196<=90 & n<=89 & postA(1+
n,v_int_15_1196)) -->  postA(n,res)]
 */
