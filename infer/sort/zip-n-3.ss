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
  infer [P]
  requires x::llN<a> * y::llN<b> & P(a,b)//a<=b
  ensures  res::llN<r> & r=a
  // R(a,b,r);
  ;
  /*
[RELDEFN P: ( b_640=b-1 & a_639=a-1 & 1<=a & 1<=b & P(a,b)) -->  P(a_639,b_640),
RELASS [P]: ( P(a,b)) -->  (b!=0 | 2>a) & (b!=0 | a!=1)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( true, true, P(a,b), (b<=(a-1) & b<=(0-1)) | a<=b)]
*************************************

!!! REL POST :  true
!!! POST:  true
!!! REL PRE :  P(a,b)
!!! PRE :  a<=b
Procedure zip$node~node SUCCESS

 */
{
  if (x==null) return null;
    else{
           x.val=x.val+y.val;
           x.next=zip(x.next, y.next);
           return x;
    }
}










