data node {
 int mark;
 node left;
 node right;
}

tx<g,s,"s":M> == true&["":self = g & s!=null & (g=null | g=s) ; "s": M={}]
   or self::node<v,l,r> * l::tx<g,s,M1> * r::tx<null,s,M2> & ["": self != g & self != s ;"s": M=union({self},M1,M2)]
   or self::node<v,l,r> * l::tx<null,s,M1> * r::tx<g,s,M2> & ["": self != g & self != s ;"s": M=union({self},M1,M2)]
inv true&["": s!=null & (g=null & self!=s | g=s & self!=null); 
       "s":(self=g & M={} | self!=g & M!={})];


void lscan(ref node cur, ref node prev, node sent)

requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a & a=null & b=sent 
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a & a=sent & b=null
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 
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
# swt-4h-addr-lbl.ss (INFO)

Both multi pre/post (4h) and case-spec (4g) are now
working with addr-lbl.ss with --lea (aggressive labelling);
running in seconds

!!!  processing primitives "["prelude.ss"]
Starting Omega...oc

Checking procedure lscan$node~node~node... 
Procedure lscan$node~node~node SUCCESS
Stop Omega... 434 invocations 
1 false contexts at: ( (31,19) )

!!! log(small):(9.406437,1761)
Total verification time: 6.076379 second(s)
	Time spent in main process: 3.920245 second(s)
	Time spent in child processes: 2.156134 second(s)
*/
