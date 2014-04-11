
data node {
	int val; 
	node next; 
}

sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or
  self::node<sm, q> * q::sll<n-1, qs, lg> & sm <= qs
  inv n >= 1 & sm <= lg & self!=null;


HeapPred H(node x, node v).
  PostPred G(node x, node v, node c).

node merge(node x, node y)
  infer [H,G]  requires H(x,y)  ensures G(x,y,res);
//	requires x::sll<n1, s1, b1> * y::sll<n2, s2, b2>
//	ensures res::sll<n1+n2, s3, b3> & s3 = min(s1, s2) & b3 = max(b1, b2);
{
  if (x == null)
    return y; 
  else  {
    if (y == null)
      return x;
    else {
      if (x.val <= y.val){
        node t = x.next;
        x.next = merge(t,y);
        return x;
      }
      else {
        node t = y.next;
        y.next = merge (x,t);
        return y;
      }
    }
  }
}
