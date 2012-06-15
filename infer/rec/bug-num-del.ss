// TODO
// inferred : 
/*
POST:  n=res+1 & 1<=a & a<=res
PRE :  1<=n
NEW RELS: [ ( a=1 & 1+res=n & 2<=n) -->  B(n,a,res), ( (1<=v_int_15_543 | v_int_15_543<=-1) & 
B(v_int_15_542,v_int_15_543,v_int_15_547) & -1+res=v_int_15_547 & -1+
a=v_int_15_543 & -1+n=v_int_15_542 & 0<=v_int_15_542) -->  B(n,a,res)]

However, precondition is too weak. Needs a recursive
precond inference.
*/
relation B(int n, int a, int r).

int del(int n, int a)
  infer /*  */ [n,B]
  requires true
  ensures  B(n,a,res); 
{  
  if (a==1) {
    acc(n);
    int n2=n-1; 
    acc(n2);
    return n2;
  } else {
    acc(n);
    return 1+del(n-1,a-1);
  }
}

void acc(int n)
  requires n>=1
  ensures true;

void acc2(int n)
  requires n>=2
  ensures true;
