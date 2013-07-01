data node {
	int val; 
	node next; 
}

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

sortHO<v,R:relation(int,int)> == self=null
  or self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) & p!=null
inv true;

llSP<R1:relation(int)> == self=null
  or self::node<v,p> * p::llSP<R1> & R1(v)
inv true;


node insert(node x, node y)
  infer [X1,X2]
  requires x::sortHO<m,X1> * y::node<v,null>
  ensures  res::sortHO<m2,X2>;
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
