data node{
	int val;
	node next;
}

HeapPred H(node a, node b, node@NI c).
HeapPred G(node a, node@NI ra, node b, node@NI rb, node@NI c).


lx<g,s> == self=g & self!=s 
  or self::node<_,nxt> * nxt::lx<g,s> & self!=g & self!=s 
  inv self!=s & (g!=self & s!=self | g=self);
//  inv self!=s;

/*
poor performance with:

//inv self!=s & (g!=self & s!=self | g=self);

Procedure lscan$node~node~node SUCCESS
Stop Omega... 147 invocations 
0 false contexts at: ()

!!! log(small):(5.886522,361)
!!! log(big)(>0.5s)(3):(6.277689,[(SAT,2.468985),(SAT,2.526955),(imply,1.281749)])
!!! 
 log(bigger)(>4s)(2):(7.184828,[(SAT:188<23:OMEGA CALCULATOR,3.912472),(SAT:287<64:OMEGA CALCULATOR,3.272356)])
Total verification time: 15.636975 second(s)
	Time spent in main process: 0.604037 second(s)
	Time spent in child processes: 15.032938 second(s)

--------
using:
  inv self!=s;
which computes:
 xform: ((g!=self & s!=self & self!=null) | (g=self & s!=self))

Procedure lscan$node~node~node SUCCESS
Stop Omega... 147 invocations 
0 false contexts at: ()

!!! log(small):(3.238215,363)
!!! log(big)(>0.5s)(1):(0.787067,[(SAT,0.787067)])
Total verification time: 3.536219 second(s)
	Time spent in main process: 0.628038 second(s)
	Time spent in child processes: 2.908181 second(s)


*/

void lscan(ref node cur, ref node prev, node sent)
 requires cur::lx<a,b> * prev::lx<b,a> & cur!=a 
   & (a=null & b=sent | a=sent & b=null)
 ensures prev'::lx<null,sent>  & cur'=sent ;

/*
requires cur::lx<null,sent> * prev::lx<sent,sent> & cur!=null 
ensures prev'::lx<null,sent>  & cur'=sent ;
requires cur::lx<sent,sent> * prev::lx<null,sent> & cur!=sent 
ensures prev'::lx<null,sent>  & cur'=sent ; 

  infer [H,G]
  requires H(cur,prev,sent)
  ensures G(cur,cur',prev,prev',sent);
*/
{

  node n;
  n = cur.next;
  // rotate ptrs
  cur.next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sent) {
      //assume false;
      return;
  }
  if (cur == null) {
      // change direction;
      cur = prev;
      dprint;
      prev = null;
      //dprint;
  }
  lscan(cur,prev,sent);

}

