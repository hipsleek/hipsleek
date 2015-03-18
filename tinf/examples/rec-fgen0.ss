// McCarthy generic 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
int f(int n, int k)
//if spec below used, term error occurs.
//requires true
//ensures true;
infer[@term]
case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=k -> requires Term[] ensures res=n;
  n<k -> 
   requires Term[k-n] 
   ensures res=k;
}
{
  if (k<=n) return n;
  else return f(f(n+1,k),k);
}

/*
# rec-fgen0.ss

Why is this example inferring fpost even though we already
specified Term in all the cases?
Are we trying to overwrite the wisdom of programmer?

Temporal Assumptions:
 termAssume res=v_int_15_1139' & v_int_15_1139'=k' & n'<k' & n<k & k'=k & 
n'=n & !(v_bool_14_1140') & n'<k' & !(v_bool_14_1140') & (1+n')<k' & 
k'<=k' & fpost_1135(1+n',k') & fpost_1134(k',k') --> fpost_1135(n,k).

 termAssume res=v_int_15_1139' & n'<k' & n<k & k'=k & n'=n & 
!(v_bool_14_1140') & n'<k' & !(v_bool_14_1140') & v_int_15_1139'=1+n' & 
k'<=v_int_15_1139' & fpost_1134(v_int_15_1138',k') & fpost_1134(v_int_15_1139',k') --> fpost_1135(n,k).

 termAssume k'<=n' & k<=n & k'=k & n'=n & v_bool_14_1140' & k'<=n' & 
v_bool_14_1140' & res=n' --> fpost_1134(n,k).

*/
