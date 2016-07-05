data node {
 int mark;
 node left;
 node right;
}

tx<"n":n,"n":g,"n":s,"s":M> == true&["n": self = g & self != s & n != s; "s": M = {}]
	or self::node<v,l,r> * l::tx<n,g,s,Ml> * r::tx<n,n,s,Mr> & ["n": self != g & self != s & n != s ; "s": M = union({self},Ml,Mr)]
	or self::node<v,l,r> * l::tx<n,n,s,Ml> * r::tx<n,g,s,Mr> & ["n": self != g & self != s & n != s ; "s": M = union({self},Ml,Mr)]
inv true&["n": self != s & n != s];

void lscan(ref node cur, ref node prev, node sentinel)
requires cur::tx<null,a,b,Mc> * prev::tx<null,b,a,Mp> & ["n": cur != a & (a=null & b=sentinel | a=sentinel & b=null)]
ensures prev'::tx<null,null,sentinel,M>  & ["n": cur' = sentinel; "s": M = union(Mc,Mp)]; 
{

  node n,tmp;
  n = cur.left;
  tmp = cur.right;
  // rotate ptrs
  cur.right = prev;
  cur.left = tmp;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sentinel) return;
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sentinel);
}

