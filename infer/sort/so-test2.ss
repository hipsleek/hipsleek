data node {
	int val; 
	node next; 
}

sortHO<v,R:relation(int,int)> == self=null
  or self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) & p!=null
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
