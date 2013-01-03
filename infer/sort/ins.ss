/* selection sort */

data node {
	int val; 
	node next; 
}

/*
ll<> == self=null
  or self::node<_,p> * p::ll<>
inv true;

llN<n> == self=null & n=0
  or self::node<v,p> * p::llN<n-1>
inv n>=0;

llS<s> == self=null & s=0
  or self::node<v,p> * p::llS<s-v>
inv true;

sortD<v> == self=null 
 or self::node<v, p> * p::sortD<v2> & v>=v2
inv true;
*/

// needs infinity
sortA<v> == self=null 
 or self::node<v,null> 
 or self::node<v, p> * p::sortA<v2> & v<=v2 & p!=null
inv true;


node insert(node x, node y)
/*
  requires x::ll<> * y::node<v,null>
  ensures  res::ll<> ;
  requires x::ll<> * y::node<v,null>
  ensures  res::ll<> & (res=x | res=y) ;
  requires x::llS<n> * y::node<v,null>
  ensures  res::llS<n+v> ;
  requires x::llN<n> * y::node<v,null>
  ensures  res::llN<n+1> ;
*/
 requires y::node<v,null>
 case {
  x=null -> ensures res::sortA<v> & res!=null;
  x!=null -> requires x::sortA<a> 
             ensures  res::sortA<b> & b=min(a,v) & res!=null;
 }
{
  if (x==null) return y;
  else {
    if (y.val<=x.val) {
        y.next = x;
        return y;
    } else {
      node tmp;
      tmp = insert(x.next,y);
      x.next=tmp;
      return x;
    }
   }
}










