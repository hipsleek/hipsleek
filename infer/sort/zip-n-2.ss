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
  infer {ll -> llN} []
  requires x::ll<> * y::ll<> 
  ensures  res::ll<>;
/*


!!! REL POST :  R_572(n_568,n_569,n_570)
!!! POST:  n_568=n_570 & 0<=n_570 & n_570<=n_569
!!! REL PRE :  R_571(n_568,n_569)
!!! PRE :  n_568<=n_569


*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_571: ( n_570=0 & n_568=0 & 0<=n_569) -->  R_571(n_568,n_569,n_570),
RELDEFN R_571: ( n_639=n_569-1 & n_638=n_568-1 & n_570=n_650+1 & 1<=n_569 & 1<=n_568 & 
0<=n_650 & R_571(n_638,n_639,n_650)) -->  R_571(n_568,n_569,n_570)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n_568; 
                  n_569](ex)x::llN<n_568>@M[0][Orig][LHSCase] * 
                  y::llN<n_569>@M[0][Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&(n_569<=(0-1) | 1<=n_569 | n_568<=0) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 66::
                              EXISTS(n_668: res::llN<n_668>@M[0][Orig][LHSCase]&
                              R_571(n_568,n_569,n_668) & 0<=n_568 & 0<=n_569&
                              {FLOW,(22,23)=__norm})[])

*/

{
  if (x==null) return null;
    else{
           x.val=x.val+y.val;
           x.next=zip(x.next, y.next);
           return x;
    }
}

/*

Checking procedure zip$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n_569!=0 | n_568<=1, n_569!=0 | n_568!=1]
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R_571: ( n_570=0 & n_568=0 & 0<=n_569) -->  R_571(n_568,n_569,n_570),
RELDEFN R_571: ( n_639=n_569-1 & n_638=n_568-1 & n_570=n_650+1 & 1<=n_569 & 1<=n_568 & 
0<=n_650 & R_571(n_638,n_639,n_650)) -->  R_571(n_568,n_569,n_570)]
*************************************

!!! post_vars:[res]
*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n_568; 
                  n_569](ex)x::llN<n_568>@M[0][Orig][LHSCase] * 
                  y::llN<n_569>@M[0][Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&(n_569<=(0-1) | 1<=n_569 | n_568<=0) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 66::
                              EXISTS(n_668: res::llN<n_668>@M[0][Orig][LHSCase]&
                              R_571(n_568,n_569,n_668) & 0<=n_568 & 0<=n_569&
                              {FLOW,(22,23)=__norm})[])
Procedure zip$node~node SUCCESS

TODO: 
- Maybe need to change the parser a bit
- Update the new-gen spec with pre-relation
*/








