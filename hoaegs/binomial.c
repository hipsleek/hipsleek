// why isn't the timeout mechanism working?
// why did verifier hang/fail for effbin?

relation bin_n(int n, int k, int r) == 
	(n = k & k>=0 & r = 1 | n>=k & k=0 & r=1 |
     n>k & k>0 & exists(r1,r2:bin_n(n-1,k,r1) & bin_n(n-1,k-1,r2) & r = r1+r2)).

relation bin(int n, int k, int r).
axiom n=k & k>=0 ==> bin(n,k,1).
axiom k=0 & n>=k ==> bin(n,k,1).
// type system cannot handle v1>v2 well - can wait..
axiom  ((n:int)>k) & k>0 & bin(n-1,k,r1) & bin(n-1,k-1,r2) ==> bin(n,k,r1+r2).

relation fact(int n, int f).
axiom n=0 ==> fact(n,1).
axiom n > 0 & fact(n-1,f1) ==> fact(n,n*f1).


relation binf(int n, int k, int r) == 
	(n = k & k>=0 & r = 1 | n>=k & k=0 & r=1 |
     n>k & k>0 & exists(r1,r2:bin_n(n-1,k,r1) & bin_n(n-1,k-1,r2) & r = r1+r2)).

int computebin(int n, int k)
  requires k>=0 & n>=k 
  ensures bin(n,k,res);
  //ensures binf(n,k,res); // hard to verify directly
{
  if (k==0 || n==k)
      {
        assume fact(0,1);
		return 1;
      }
  else {
      return computebin(n-1,k-1)+computebin(n-1,k);
    }
}

axiom n=k & k>=0 ==> binf(n,k,1).
axiom k=0 & n>=k ==> binf(n,k,1).
axiom n>k & k>0 & fact(n,r1) & fact(k,r2) & fact(n-k,r3) &
  r*r2*r3 = r1 ==> binf(n,k,r).

int effbin(int n, int k)
 requires k>=0 & n>=k 
 case {
  k=0 -> ensures res=1;
  k!=0 -> case {
    n=k -> ensures res=1;
    n!=k -> ensures binf(n,k,res);
  }
 }
{
  if (n==k || k==0) 
    {
      //assume fact(0,1);
      return 1;
    }
    else {
      //assume false; //does not verify without
      int r = (n * effbin(n-1,k-1))/k;
      //dprint;
      //assume false;
      return r;
    }

}

/*

int fact2(int n)
  requires n>=0
  ensures facta(n,res);
{
  assume facta(0,1);
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
  assume facta(0,1);
  while (n>0) 
    requires n>=0 
    ensures (exists f0: facta(n,f0) & r'=r*f0 & n'=0);
    {
      r = n*r;
      n = n-1;
    }
  return r;
}
*/
