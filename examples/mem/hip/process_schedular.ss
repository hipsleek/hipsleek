data node{
int id;
int status;
node next;
node rnext;
node snext;
}

ll<R> == self = null & R = {}
	or self::node<_@L,v@L,p,_@A,_@M> * p::ll<Rp> & R = union(Rp,{self}) & v = 1
	or self::node<_@L,v@L,p,_@M,_@A> * p::ll<Rp> & R = union(Rp,{self}) & v != 1
	inv true
    mem R->(node<@L,@L,@M,@A,@M> | node<@L,@L,@M,@M,@A>);
    
rll<R> == self = null & R = {}
	or self::node<_@L,v@L,_@A,p,_@A> * p::rll<Rp> & R = union(Rp,{self}) & v = 1
	inv true
    mem R->(node<@L,@L,@A,@M,@A>);
    
sll<R> == self = null & R = {}
	or self::node<_@L,v@L,_@A,_@A,p> * p::sll<Rp> & R = union(Rp,{self}) & v != 1
	inv true
    mem R->(node<@L,@L,@A,@A,@M>);
    
void insert_process(int pid, int stat, ref node plist, ref node rlist, ref node slist)
case {
stat = 1 -> requires plist::ll<R> & rlist::rll<R1> * slist::sll<R2> & R = union(R1,R2)
	    ensures plist'::ll<Rp> & rlist'::rll<R1p> * slist::sll<R2> 
	    & plist' = rlist' & Rp = union(R1p,R2) & R1p = union(R1,{rlist'}) & Rp = union(R,{plist'});
stat != 1 -> requires plist::ll<R> & rlist::rll<R1> * slist::sll<R2> & R = union(R1,R2)
	    ensures plist'::ll<Rp> & rlist::rll<R1> * slist'::sll<R2p>
	    & plist' = slist' & Rp = union(R1,R2p) & R2p = union(R2,{slist'}) & Rp = union(R,{plist'});}
{
	node tmp = new node(pid,stat,null,null,null);
	//tmp.next = plist;
	//plist = tmp;
	if(stat == 1){
		rlist = insert_rll(rlist,tmp);
		}
	else{
		slist = insert_sll(slist,tmp);
		}
	dprint;
	plist = insert_pll(plist,tmp);
}

node insert_pll(node x, ref node n)
requires x::ll<R> * n::node<_@L,1@L,_@M,_@A,_@M>
ensures res::ll<R1> & R1 = union(R,{n});
requires x::ll<R> * n::node<_@L,v@L,_@M,_@M,_@A> & v != 1
ensures res::ll<R1> & R1 = union(R,{n});
{
	n.next = x;
	return n;
}

node insert_rll(node x, ref node n)
requires x::rll<R> * n::node<_@L,1@L,_@A,_@M,_@A>
ensures res::rll<R1> & R1 = union(R,{n});
{
	n.rnext = x;
	return n;
}

node insert_sll(node x, ref node n)
requires x::sll<R> * n::node<_@L,v@L,_@A,_@A,_@M> & v != 1
ensures res::sll<R1> & R1 = union(R,{n});
{
	n.snext = x;
	return n;
}

