data node {
 int mark;
 node left;
 node right;
}


tx<g,s,M> == self = g & s!=null & (g=null | g=s) & M={}
   or self::node<v,l,r> * l::tx<g,s,M1> * r::tx<null,s,M2> & self != g & self != s & M=union({v},M1,M2)
   or self::node<v,l,r> * l::tx<null,s,M1> * r::tx<g,s,M2> & self != g & self != s & M=union({v},M1,M2)
inv s!=null & (g=null & self!=s | g=s & self!=null)
 ;

tr<s,M> == self = null & s!=null & M={}
   or self::node<v,l,r> * l::tr<s,M1> * r::tr<s,M2> & self != s & M=union({v},M1,M2)
   or self::node<v,l,r> * l::tr<s,M1> * r::tr<s,M2> & self != s & M=union({v},M1,M2)
inv s!=null &  self!=s
 ;

ts<s,M> == self = s & s!=null  & M={}
   or self::node<v,l,r> * l::ts<s,M1> * r::tr<s,M2> & self != s & M=union({v},M1,M2)
   or self::node<v,l,r> * l::tr<s,M1> * r::ts<s,M2> & self != s & M=union({v},M1,M2)
inv s!=null & self!=null
 ;

void lscan(ref node cur, ref node prev, node sent)
requires cur::tr<sent,M1> * prev::ts<sent,M2> & cur != null
ensures prev'::tr<sent,union(M1,M2)>  & cur' = sent; 
requires cur::ts<sent,M1> * prev::tr<sent,M2> & cur != sent
ensures prev'::tr<sent,union(M1,M2)>  & cur' = sent; 
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

/*
!!! time_log (small):(16.71916,1295)
!!! log (>.5s):(105.412322,[0.579521,0.591007,0.620163,4.623546,4.630001,0.93692,0.62353,1.515439,0.917639,1.317985,0.501701,1.248417,0.568656,0.571321,0.56384,0.572376,0.611973,0.613186,31.68598,31.773986,4.75746,1.516423,0.707189,0.956254,0.667541,1.589292,1.200452,0.900657,1.180471,1.33619,0.964613,1.199119,0.783068,0.894799,0.800144,0.891463])
Total verification time: 60.575783 second(s)
	Time spent in main process: 4.152258 second(s)
	Time spent in child processes: 56.423525 second(s)
	Time for logging: 1.468093 second(s)
*/