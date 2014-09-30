data node {
 int mark;
 node left;
 node right;
}


tx<g,s> == self = g & s!=null & (g=null | g=s)
   or self::node<_,l,r> * l::tx<g,s> * r::tx<null,s> & self != g & self != s 
   or self::node<_,l,r> * l::tx<null,s> * r::tx<g,s> & self != g & self != s 
inv s!=null & (g=null | g=s)
 ;

tr<s> == self = null & s!=null 
   or self::node<_,l,r> * l::tr<s> * r::tr<s> & self != s 
   or self::node<_,l,r> * l::tr<s> * r::tr<s> & self != s 
inv s!=null 
 ;

ts<s> == self = s & s!=null 
   or self::node<_,l,r> * l::ts<s> * r::tr<s> & self != s 
   or self::node<_,l,r> * l::tr<s> * r::ts<s> & self != s 
inv s!=null 
 ;

void lscan(ref node cur, ref node prev, node sent)
requires cur::tr<sent> * prev::ts<sent> & cur != null
ensures prev'::tr<sent>  & cur' = sent; 
requires cur::ts<sent> * prev::tr<sent> & cur != sent
ensures prev'::tr<sent>  & cur' = sent; 
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
  if (cur == sent) return;
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sent);
}

