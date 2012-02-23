data node {
	int val; 
	node next;	
}

sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
  or (exists qs,ql: self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql = lg & sm = qmin )
  inv n >= 0 & sm <= lg;

relation D(int a, int b, int c, int m, int n, int p, int q).
relation C(int a, int b, int c).

void append_sll(node x, node y)
  infer [xl,ys,xn,D]
  requires x::sll<xn,xs,xl> * y::sll<yn,ys,yl>
  //ensures x::sll<m,xs,yl> & m=xn+yn; 
  //ensures x::sll<m,xs,yl> & C(m,xn,yn);
  ensures x::sll<m,r,t> & D(r,xs,t,yl,m,xn,yn);
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

