/* selection sort */

data node {
	int val; 
	node next; 
}

// needs infinity

ls<v> == 
  self::node<v,null> 
  or self::node<v, p> * p::ls<v2>  
inv self!=null;

sortHO<v,R:relation(int,int)> == 
  self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) 
inv self!=null;

relation R0(int r, int a).
relation R1(int r, int a) == r<=a.

relation RRR(int r, int a) == r<=a .
relation LT(int r, int a) == r>a .

node insert(node x, node y)
  requires x::sortHO<a,RRR> * y::node<v,null>
  ensures  res::sortHO<b,RRR> & (v>a & b=a | (a>=b & b=v));

node sort(node x)
     requires x::ls<a>
     ensures  res::sortHO<b,RRR> & b<=a ;
{
    node tmp = x.next;
    if (tmp==null) return x;
    else {
      x.next=null;
      tmp=sort(tmp);
      return insert(tmp,x);
    }
}

