data node{
int id;
int status;
node next;
node rnext;
node snext;
}

ll<R> == self = null & R = {}
	or self::node<_@L,v@L,p,_@M,_@A> * p::ll<Rp> & R = union(Rp,{self}) & v = 1
	or self::node<_@L,v@L,p,_@A,_@M> * p::ll<Rp> & R = union(Rp,{self}) & v = 2
	inv true
    mem R->(node<@L,@L,@M,@M,@A> | node<@L,@L,@M,@A,@M>);
    
rll<R> == self = null & R = {}
	or self::node<_@L,v@L,_@A,p,_@A> * p::rll<Rp> & R = union(Rp,{self}) & v = 1
	inv true
    mem R->(node<@L,@L,@A,@M,@A>);
    
sll<R> == self = null & R = {}
	or self::node<_@L,v@L,_@A,_@A,p> * p::rll<Rp> & R = union(Rp,{self}) & v = 2
	inv true
    mem R->(node<@L,@L,@A,@A,@M>);
    
void insert_process(int pid, int stat, ref node plist, ref node rlist, ref node slist)
case {
stat = 1 -> requires (plist::ll<R> & rlist::rll<R1> * slist::sll<R2>) & R = union(R1,R2)
	    ensures (plist'::ll<Rp> & rlist'::rll<Rr> * slist::sll<R2>) & plist' = rlist' & Rp = union(Rr,R2);
stat != 1 -> ensures (plist'::ll<Rp> & rlist::rll<R1> * slist'::sll<Rs>) & plist' = slist' & Rp = union(Rs,R1);}
{
	node tmp = new node(pid,stat,null,null,null);
	tmp.next = plist;
	plist = tmp;
	if(stat == 1)
		rlist = insert_rll(rlist,tmp);
	else
		slist = insert_sll(slist,tmp);		
}

node insert_rll(node x, node n)
requires x::rll<R> * n::node<_@L,_@L,_@A,_@M,_@A>
ensures n::rll<Rr> & Rr = union(R,{n});
{
	n.rnext = x;
	return n;
}

node insert_sll(node x, node n)
requires x::sll<R> * n::node<_@L,_@L,_@A,_@A,_@M>
ensures n::sll<Rr> & Rr = union(R,{n});
{
	n.snext = x;
	return n;
}

