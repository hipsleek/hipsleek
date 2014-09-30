relation fact(int n, int f) == 
	(n = 0 & f = 1 |
	n >= 1 & exists(f1 : fact(n-1,f1) & f = n*f1)).

relation facta(int n, int f).

axiom true ==> facta(0,1).
axiom n > 0 & facta(n-1,f1) ==> facta(n,n*f1).

  /*
wrong message:
ERROR: at File "fact.c",Line:49,Col:11 
Message: existential vars should not be primed
   */
int factit3(int n, int acc)
  requires n >= 0
  //ensures (exists f0: facta(n,f0) & res=acc*f0 & n'=0);//'
  ensures (exists f0: facta(n,f0) & res=acc*f0);//'
{
	if (n==0)
		return acc;
	else
      return factit3(n-1,n*acc);
}

/*
redundant messages:
Context of Verification Failure: File "fact-bugs.c",Line:18,Col:11
Last Proving Location: File "fact-bugs.c",Line:23,Col:13

Context of Verification Failure: File "fact-bugs.c",Line:18,Col:11
Last Proving Location: File "fact-bugs.c",Line:23,Col:13
*/


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
