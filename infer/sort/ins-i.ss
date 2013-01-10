/* selection sort */

data node {
	int val; 
	node next; 
}

relation R0(node x, node y, node z).
relation R1(int a, int b, int c).
relation R2(int a, int b).
relation R3(int a, int b, int c).

ll<> == self=null
  or self::node<_,p> * p::ll<>
inv true;

llN<n> == self=null & n=0
  or self::node<v,p> * p::llN<n-1>
inv n>=0;

llS<s> == self=null & s=0
  or self::node<v,p> * p::llS<s-v>
inv true;

sortA<v> == self=null
 or self::node<v,null> 
 or self::node<v, p> * p::sortA<v2> & v<=v2 & p!=null
inv true;

sortD<v> == self=null 
 or self::node<v, p> * p::sortD<v2> & v>=v2
inv true;

node insert(node x, node y)
  infer [R0]
  requires x::ll<> * y::node<v,null>
  ensures  res::ll<> & R0(res,x,y);
/*
 !!! REL POST :  R0(res,x,y)
!!! POST:  (res=x & x!=null & y!=null) | (res=y & y!=null)
!!! REL PRE :  true
!!! PRE :  true

*/
/*
  infer [R1]
  requires x::llS<s> * y::node<v,null>
  ensures  res::llS<s2> & R1(s2,s,v) ;
*************************************
*******fixcalc of pure relation *******
*************************************
[( R2(m,n), n>=0 & m=n+1),
( R1(s2,s,v), s2=s+v)]
*************************************
*/
/*
  infer [R2]
  requires x::llN<n> * y::node<v,null>
  ensures  res::llN<m> & R2(m,n) ;

!!! REL :  R2(m,n)
!!! POST:  n>=0 & m=n+1
!!! PRE :  true
TODO : maybe can remove n>=0 from the inference
*/

/*
  infer [R3]
  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & R3(b,a,v); 
  // expecting (b=v | b=a) ;

inferred an even better result!
!!! REL :  R3(b,a,v)
!!! POST:  b=v | (v>=(1+a) & a=b)
!!! PRE :  true

*/
{
  if (x==null) return y;
  else {
    int t = x.val;
    if (y.val<=x.val) {
        y.next = x;
        return y;
    } else {
      node tmp;
      tmp = insert(x.next,y);
      //assume tmp'=null or tmp'!=null;
      x.next=tmp;
      return x;
    }
   }
}










