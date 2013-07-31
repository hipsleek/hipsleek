data node {
 int mark;
 node left;
 node right;
}

tx<g,s,"s":M> == true&["":self = g & s!=null & (g=null | g=s) ; "s": M={}]
   or self::node<v,l,r> * l::tx<g,s,M1> * r::tx<null,s,M2> & ["": self != g & self != s ;"s": M=union({self},M1,M2)]
   or self::node<v,l,r> * l::tx<null,s,M1> * r::tx<g,s,M2> & ["": self != g & self != s ;"s": M=union({self},M1,M2)]
inv true&["": s!=null & (g=null & self!=s | g=s & self!=null); 
"s"://s notin M  &
(self=g & M={} | self!=g & M!={} //& self in M
)];


void lscan(ref node cur, ref node prev, node sent)
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> 
 case { 
    a=null ->
       case { 
         b=sent & cur!=null ->
            ensures prev'::tx<null,sent,M3>  & ["": cur' = sent 
            & prev'!=null 
            ; "s": M3=union(M1,M2)]; 
         b!=sent | cur=null -> 
            requires false
            ensures false;
        }
    a!=null ->
       case { 
         b=null & cur!=sent & a=sent ->
             ensures prev'::tx<null,sent,M3>  & ["": cur' = sent 
               & prev'!=null 
              ;"s": M3=union(M1,M2)];
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
           //assume false;
           return;
  }
  if (cur == null) {
      // change direction;
      //assume false;
      cur = prev;
      prev = null;
  } else {
      assume true;
  }
  lscan(cur,prev,sent);
}

