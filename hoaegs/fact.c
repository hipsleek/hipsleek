relation fact(int n, int f) == 
	(n = 0 & f = 1 |
	n >= 1 & exists(f1 : fact(n-1,f1) & f = n*f1)).

relation facta(int n, int f).
// using n=0 avoided some assume
axiom n=0 ==> facta(n,1).
axiom n > 0 & facta(n-1,f1) ==> facta(n,n*f1).

int computefact(int n)
	requires n >= 0
    ensures facta(n,res);
//ensures fact(n,res);
{
	if (n <= 1)
		return 1;
	else
      return n*computefact(n-1);
}

int fact2(int n)
  requires n>=0
  ensures facta(n,res);
{
  //assume facta(0,1);
  return factit(n,0,1);
}

/*
// how to fix this error?
Verification Context:(Line:31,Col:12)
Proving precondition in method factit$int~int~int for spec:
 EBase true & facta(v_int_36_786',v_int_36_785') & 0<=v_int_36_786' & 
       0<=v_int_36_787' & {FLOW,(20,21)=__norm}
         EAssume 7::
           true & facta(v_int_36_786'+v_int_36_787',res) &
           {FLOW,(20,21)=__norm} has failed 

*/
int factit(int n, int m, int acc)
    requires facta(m,acc) & m>=0 & n>=0
    ensures facta(m+n,res);
{
	if (n==0)
		return acc;
	else
      {
        int k=m+1; // causes a verification bug when k not present
        return factit(n-1,k,k*acc);
      }
}

int fact3(int n)
  requires n>=0
  ensures facta(n,res);
{
  return factit3(n,1);
}


int factit3(int n, int acc)
  requires n >= 0
  ensures (exists f0: facta(n,f0) & res=acc*f0);//'
{
	if (n==0)
		return acc;
	else
      return factit3(n-1,n*acc);
}

int fact_while(int n)
    requires n>=0
    ensures facta(n,res);
{
  int r = 1;
  //assume facta(0,1);
  while (n>0) 
    requires n>=0 
    ensures (exists f0: facta(n,f0) & r'=r*f0 & n'=0);
    {
      r = n*r;
      n = n-1;
    }
  return r;
}
