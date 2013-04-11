data node{
int val;
node next;
node tnext;
}

lln<hd,R> == self = hd & R = {}
	or self::node<_@L,p,_@A> * p::lln<hd,Rp> & R = union(Rp,{self}) & self != hd 
	inv true
    	memE R->(node<@L,@M,@A>);
    
llt<hd,R> == self = hd & R = {}
	or self::node<_@L,_@A,p> * p::llt<hd,Rp> & R = union(Rp,{self}) & self != hd 
	inv true
    	memE R->(node<@L,@A,@M>);
    
   
void insert_dcll(int v, ref node x)
requires x::node<0,y,z> * (y::lln<x,R> &* z::llt<x,R>)
ensures x'::node<v,y@A,z@A> * (y::lln<x',Ru> &* z::llt<x',Ru>) & x = y & x = z;
{
	node tmp = new node(v,null,null);
	x.next = insert_lln(x,tmp);
	x.tnext = insert_llt(x,tmp);
	x = tmp;
dprint;
}

node insert_lln(node x, node n)
requires x::lln<hd,R> * n::node<v@L,_@M,_@A>
ensures res::lln<hd,R1> & R1 = union(R,{n});
{
	n.next = x;
	return n;
}

node insert_llt(node x, node n)
requires x::llt<hd,R> * n::node<v@L,_@A,_@M>
ensures res::llt<hd,R1> & R1 = union(R,{n});
{
	n.tnext = x;
	return n;
}

