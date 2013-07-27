data node {
 int mark;
 node left;
 node right;
}

tx<g,s,M> == self = g & s!=null & (g=null | g=s) & M={}
   or self::node<v,l,r> * l::tx<g,s,M1> * r::tx<null,s,M2> & self != g & self != s & M=union({v},M1,M2)
   or self::node<v,l,r> * l::tx<null,s,M1> * r::tx<g,s,M2> & self != g & self != s & M=union({v},M1,M2)
inv s!=null & (g=null & self!=s | g=s & self!=null) & (self=g & M={} | self!=g & M!={});


void lscan(ref node cur, ref node prev, node sent)
/*
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a & a=null & b=sent 
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a & a=sent & b=null
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 


requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a &
        (a=null & b=sent | a=sent & b=null)
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 
*/
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
      //assume false;
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sent);
}

