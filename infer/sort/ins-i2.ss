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
 or self::node<v,null> 
 or self::node<v, p> * p::sortD<v2> & v>=v2 & p!=null
inv true;

// list with sorted elements
sortHO<v,R:relation(int,int)> == self=null
  or self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) & p!=null
inv true;

// list with positive elements
llSP<R:relation(int)> == self=null
  or self::node<v,p> * p::llSP<R> & R(v)
inv true;

node insert(node x, node y)
  infer [X1,X2,R1]
  requires x::sortHO<m,X1> * y::node<v,null>
  ensures  res::sortHO<m2,X2> & R1(m2,v,m);
/*
 expecting X1(a,b) :- a<=b
 expecting X2(a,b) :- a<=b
 R0(m2,v,m) :- m2=v | v<m & m2=v  (m2=min(v,m)
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










