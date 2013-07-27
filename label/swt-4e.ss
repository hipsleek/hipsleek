data node {
 int mark;
 node left;
 node right;
}

/*
tx<g,s,M> == self = g & s!=null & (g=null | g=s) & M={}
   or self::node<v,l,r> * l::tx<g,s,M1> * r::tx<null,s,M2> & self != g & self != s & M=union({v},M1,M2)
   or self::node<v,l,r> * l::tx<null,s,M1> * r::tx<g,s,M2> & self != g & self != s & M=union({v},M1,M2)
inv s!=null & (g=null & self!=s | g=s & self!=null)
 ;
*/

tx<g,s> == self = g & s!=null & (g=null | g=s)
   or self::node<_,l,r> * l::tx<g,s> * r::tx<null,s> & self != g & self != s 
   or self::node<_,l,r> * l::tx<null,s> * r::tx<g,s> & self != g & self != s 
inv s!=null & (g=null & self!=s | g=s & self!=null)
 ;


void lscan(ref node cur, ref node prev, node sent)
/*
requires cur::tx<null,sent> * prev::tx<sent,sent> & cur != null
ensures prev'::tx<null,sent>  & cur' = sent; 
requires cur::tx<sent,sent> * prev::tx<null,sent> & cur != sent
ensures prev'::tx<null,sent>  & cur' = sent; 
*/
requires cur::tx<a,sent> * prev::tx<b,sent> 
 case { 
    a=null ->
       case { 
         b=sent ->
            requires cur!=null
            ensures prev'::tx<null,sent>  & cur' = sent & prev'!=null;
         b!=sent -> 
            requires false
            ensures false;
        }
    a!=null ->
       case { 
         b=null & a=sent ->
            requires cur!=sent
            ensures prev'::tx<null,sent>  & cur' = sent & prev'!=null;
         b!=null | a!=sent -> 
            requires false
            ensures false;
        }
  }
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

