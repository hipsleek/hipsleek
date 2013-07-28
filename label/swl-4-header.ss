data node{
	int val;
	node next;
}


lx<"n":g,"n":s,"S":M> == true & ["n":self=g & self!=s; "S": M={}]
  or self::node<v,nxt> * nxt::lx<g,s,M1> & ["n":self!=g & self!=s; "S": M=union(M1,{self})]
  inv true & ["n":self!=s]  ;

void lscan(ref node cur, ref node prev, node sent)
 requires cur::lx<a,b,M1> * prev::lx<b,a,M2> & ["n":cur!=a & (a=null & b=sent | a=sent & b=null)]
 ensures prev'::lx<c,sent,M3>  & ["n":c=null & cur'=sent; "S":M3=union(M1,M2)];

