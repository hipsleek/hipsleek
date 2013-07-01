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
  infer [R,P]
  requires x::llN<a> * y::llN<b> & 
  //a<=b
  P(a,b)
  ensures  res::llN<r> & 
  // r=a
  R(a,b,r)
  ;
  /*
[RELDEFN P: ( b_639=b-1 & a_638=a-1 & 1<=a & 1<=b & P(a,b)) -->  P(a_638,b_639),
RELASS [P]: ( P(a,b)) -->  b!=0 | 1>a,
RELDEFN R: ( r=0 & a=0 & 0<=b & P(a,b)) -->  R(a,b,r),
RELDEFN R: ( b_639=b-1 & a_638=a-1 & r=r_651+1 & 1<=b & 1<=a & 0<=r_651 & P(a,b) & 
R(a_638,b_639,r_651)) -->  R(a,b,r)]


 */
{
  if (x==null) return null;
    else{
           x.val=x.val+y.val;
           x.next=zip(x.next, y.next);
           return x;
    }
}










