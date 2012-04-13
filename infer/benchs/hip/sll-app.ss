data node {
	int val; 
	node next;	
}

sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
  or (exists qs: self::node<sm, q> * q::sll<n-1, qs, lg> & sm <= qs)
  inv n >= 0 & sm <= lg;

relation D(int a, int b, int m, int n, int p, int q).
relation C(int a, int b, int c).

void append_sll(node x, node y)
  infer [xl,ys,xs,yl,D]
  requires x::sll<xn,xs,xl> * y::sll<yn,ys,yl> & x!=null
  //ensures x::sll<m,xs,yl> & m=xn+yn; 
  //ensures x::sll<m,xs,yl> & C(m,xn,yn);
  ensures x::sll<xn+yn,r,t> & D(r,xs,t,yl,xl,ys);
{
  if (x.next == null) {
    x.next = y;
    //dprint;
  }
  else {
    //assume false;
    append_sll(x.next, y);
    //dprint;
  }
}


