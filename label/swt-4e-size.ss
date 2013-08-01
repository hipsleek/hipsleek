data node {
 int mark;
 node left;
 node right;
}

tx<g,s,M> == self = g & s!=null & (g=null | g=s) & M=0
   or self::node<v,l,r> * l::tx<g,s,M1> * r::tx<null,s,M2> & self != g & self != s & M=1+M1+M2
   or self::node<v,l,r> * l::tx<null,s,M1> * r::tx<g,s,M2> & self != g & self != s & M=1+M1+M2
inv M>=0 & s!=null & (g=null & self!=s | g=s & self!=null)
  & (self=g & M=0 | self!=g & M>0)
 ;

void lscan(ref node cur, ref node prev, node sent)
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> 
 case { 
    a=null ->
       case { 
         b=sent ->
            requires cur!=null
            ensures prev'::tx<null,sent,M1+M2>  & cur' = sent 
              & prev'!=null; 
         b!=sent -> 
            requires false
            ensures false;
        }
    a!=null ->
       case { 
         b=null & a=sent ->
            requires cur!=sent
             ensures prev'::tx<null,sent,M1+M2>  & cur' = sent 
              & prev'!=null; 
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
  if (cur == sent) {
        //assume false;
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

