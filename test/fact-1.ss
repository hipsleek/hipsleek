relation ff(int n, int r).

int aux(int n)
 infer [ff]
 requires n>=0
  ensures ff(n,res);
//ff(n,res);
{
  if (n==0) return 0;
  else return n + aux(n-1);
}

/*

[RELDEFN ff: ( n=0 & res=0) -->  ff(n,res),
RELDEFN ff: ( ff(v_int_10_1190,v_int_10_1192) & v_int_10_1190=n-1 & res=n+v_int_10_1192 & 
 1<=n) -->  ff(n,res)]

 */.
