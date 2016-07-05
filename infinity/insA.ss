/* selection sort */

data node {
	int val; 
	node next; 
}

//relation O(int m, int n).
relation R(int w, int m, int n).

sortll<mi,n> == self=null & mi=\inf & n=0 or
  self::node<mi, p> * p::sortll<m2,n-1> & mi<=m2 //& O(mi,m2)
inv n>=0;

node insert(node x, node y)
  //infer [R]
  requires x::sortll<mn,n> * y::node<v,null>
  //ensures  res::sortll<w,n+1> & R(w,v,mn);
  ensures  res::sortll<w,n+1> & w=min(v,mn) ;
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
      x.next=tmp;
      return x;
    }
   }
}










