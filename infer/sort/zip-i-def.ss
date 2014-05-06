/* selection sort */

data node {
	int val; 
	node next; 
}

ll<> == self=null
  or self::node<_,p> * p::ll<>
inv true;

llN<n> == self=null & n=0
  or self::node<v,p> * p::llN<n-1>
inv n>=0;

relation R(int a,int b,int c).
relation P(int a,int b).

node zip(node x, node y)
  infer [a,b,R]
  requires x::llN<a> * y::llN<b>
  ensures  res::llN<r> & R(a,b,r);
  /*

same as zip-i-2.ss

WHY not mention pre is 0<=a & a<=b

!!! REL POST :  R(a,b,r)
!!! POST:  a=r & 0<=r & r<=b
!!! REL PRE :  true
!!! PRE :  true
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[a; 
                  b](ex)x::llN<a>@M[0][Orig][LHSCase] * 
                  y::llN<b>@M[0][Orig][LHSCase]&true&{FLOW,(22,23)=__norm}[]
                    EBase emp&(1<=b | b<=(0-1) | a<=0) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 66::
                              EXISTS(r: res::llN<r>@M[0][Orig][LHSCase]&

 */
{
  if (x==null) return null;
  else {
    bind x to (xv,xn) in
    {
      bind y to (yv,yn) in
      { xv = xv+yv;
        xn = zip(xn,yn);
      }
    }
    return x;
  }
}










