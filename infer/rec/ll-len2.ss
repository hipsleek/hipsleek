data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation R(int n, int m).

int length(node x)
  infer /*  */ [R]
  requires x::ll<n>@L
  case {
    n=0 -> ensures R(n,res);
    n!=0 -> ensures R(n,res);
  }
  // R(res,n) = res=n
{
  if (x==null) return 0;
  else {
    int r = length(x.next);
    return 1+r;
  }
}

/*
TODO : false as postcondition is too strong! Thus, I suggest
that if rel is detected at ensures, we do not compute its fixpoint
until the end of the method spec.

NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         ECase case {
                n=0 -> EAssume 1::
                         true & n=0 & res=0 & n=0 & 0<=n &
                         {FLOW,(20,21)=__norm}
                ;
                n!=0 -> EAssume 2::
                          false & false & {FLOW,(20,21)=__norm} 
                }


*/

