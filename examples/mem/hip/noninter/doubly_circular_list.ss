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
    
   
void insert_dcll(int v, node x)
requires x::node<0,y,z> * (y::lln<x,R> &* z::llt<x,R>)
ensures  x::node<0,i,j> * (i::lln<x,Ru> &* j::llt<x,Ru>) & R subset Ru;
{
	node tmp = new node(v,null,null);
	x.next = insert_lln(x.next,tmp);
	x.tnext = insert_llt(x.tnext,tmp);
}

void insert_node_dcll(node v, node x)
requires x::node<0,y,z> * v::node<m,_,_> * (y::lln<x,R> &* z::llt<x,R>)
ensures  x::node<0,i,j> * (i::lln<x,Ru> &* j::llt<x,Ru>) & Ru = union(R,{v});
{
	//node tmp = new node(v,null,null);
	x.next = insert_lln(x.next,v);
	x.tnext = insert_llt(x.tnext,v);
}

node insert_lln(node x, node n)
requires x::lln<hd,R> * n::node<v@L,_@M,_@A> & n != hd
ensures res::lln<hd,R1> & R1 = union(R,{n});
{
	n.next = x;
	return n;
}

node insert_llt(node x, node n)
requires x::llt<hd,R> * n::node<v@L,_@A,_@M> & n != hd
ensures res::llt<hd,R1> & R1 = union(R,{n});
{
	n.tnext = x;
	return n;
}

