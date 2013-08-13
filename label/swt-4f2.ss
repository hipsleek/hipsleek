data node {
 int mark;
 node left;
 node right;
}

tx<g,s> == self = g & s!=null & (g=null | g=s) 
   or self::node<v,l,r> * l::tx<g,s> * r::tx<null,s> & self != g & self != s 
   or self::node<v,l,r> * l::tx<null,s> * r::tx<g,s> & self != g & self != s 
inv s!=null & (g=null & self!=s | g=s & self!=null)
//  & (self=g & M={} | self!=g & M!={})
 ;


void lscan(ref node cur, ref node prev, node sent)

requires cur::tx<a,sent> * prev::tx<b,sent> & cur != a & a=null & b=sent 
ensures prev'::tx<null,sent>  & cur' = sent & prev'!=null; 
requires cur::tx<a,sent> * prev::tx<b,sent> & cur != a & a=sent & b=null
ensures prev'::tx<null,sent>  & cur' = sent & prev'!=null; 
/*
  multi pre/post seems critical in above which wasn't the
  case for list example

requires cur::tx<a,sent> * prev::tx<b,sent> & cur != a &
        (a=null & b=sent | a=sent & b=null)
ensures prev'::tx<null,sent>  & cur' = sent & prev'!=null; 

requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> 
 case { 
    a=null ->
       case { 
         b=sent & cur!=null ->
            ensures prev'::tx<null,sent,M3>  & cur' = sent & M3=union(M1,M2) 
              & prev'!=null; 
         b!=sent | cur=null -> 
            requires false
            ensures false;
        }
    a!=null ->
       case { 
         b=null & cur!=sent & a=sent ->
             ensures prev'::tx<null,sent,M3>  & cur' = sent & M3=union(M1,M2)
              & prev'!=null; 
         b!=null | cur=sent | a!=sent -> 
            requires false
            ensures false;
        }
  }
*/
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
  if (cur == sent) {
        return;
  }
  if (cur == null) {
      assume false;
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sent);
}

