data node{
int id;
int status;
node next;
node rnext;
node snext;
}

ll<R> == self = null & R = {}
	or self::node<_@L,v@L,p,_@A,_@A> * p::ll<Rp> & R = union(Rp,{self}) 
	inv true
    memE R->(node<@L,@L,@M,@A,@A>);
    
rll<R> == self = null & R = {}
	or self::node<_@L,v@L,_@A,p,_@A> * p::rll<Rp> & R = union(Rp,{self}) & v = 1
	inv true
    memE R->(node<@L,@L,@A,@M,@A>);
    
sll<R> == self = null & R = {}
	or self::node<_@L,v@L,_@A,_@A,p> * p::sll<Rp> & R = union(Rp,{self}) & v != 1
	inv true
    memE R->(node<@L,@L,@A,@A,@M>);

all<v,R> == self = null & R = {}
	or self::node<_@L,d@L,p,_@A,_@A> * p::all<1,Rp> & R = union(Rp,{self}) & v = 1 
	or self::node<_@L,d@L,_@A,p,_@A> * p::all<2,Rp> & R = union(Rp,{self}) & v = 2 & d = 1
	or self::node<_@L,d@L,_@A,_@A,p> * p::all<3,Rp> & R = union(Rp,{self}) & v = 3 & d != 1;

void insert_process2(int pid, int stat, ref node plist, ref node rlist, ref node slist)
case {
stat = 1 -> requires rlist::all<2,R1> * slist::all<3,R2> * plist::all<1,R>  & R = union(R1,R2)
	    ensures  rlist'::all<2,R1p> * slist::all<3,R2> * plist'::all<1,Rp>
      	& plist' = rlist' & Rp = union(R1p,R2) & R1p = union(R1,{rlist'}) & Rp = union(R,{plist'});
stat != 1 -> requires rlist::all<2,R1> * slist::all<3,R2> * plist::all<1,R> & R = union(R1,R2)
	    ensures rlist::all<2,R1> * slist'::all<3,R2p> * plist'::all<1,Rp> 
	    & plist' = slist' & Rp = union(R1,R2p) & R2p = union(R2,{slist'}) & Rp = union(R,{plist'});}
{
	node tmp = new node(pid,stat,null,null,null);
	tmp.next = plist;
	plist = tmp;
	if(stat == 1){
		rlist = insert_rll2(rlist,tmp);
		}
	else{ 
		slist = insert_sll2(slist,tmp);
		}
}

node insert_rll2(node x, node n)
requires x::all<2,R> * n::node<_@L,1@L,_@A,_@M,_@A>
ensures res::all<2,R1> & R1 = union(R,{n}) & res = n;
{
	n.rnext = x;
	return n;
}

node insert_sll2(node x, node n)
requires x::all<3,R> * n::node<_@L,v@L,_@A,_@A,_@M> & v != 1
ensures res::all<3,R1> & R1 = union(R,{n}) & res = n;
{
	n.snext = x;
	return n;
}

    
void insert_process(int pid, int stat, ref node plist, ref node rlist, ref node slist)
case {
stat = 1 -> requires rlist::rll<R1> * slist::sll<R2> &* plist::ll<R>  & R = union(R1,R2)
	    ensures  rlist'::rll<R1p> * slist::sll<R2> &* plist'::ll<Rp>
      	& plist' = rlist' & Rp = union(R1p,R2) & R1p = union(R1,{rlist'}) & Rp = union(R,{plist'});
stat != 1 -> requires rlist::rll<R1> * slist::sll<R2> &* plist::ll<R> & R = union(R1,R2)
	    ensures rlist::rll<R1> * slist'::sll<R2p> &* plist'::ll<Rp> 
	    & plist' = slist' & Rp = union(R1,R2p) & R2p = union(R2,{slist'}) & Rp = union(R,{plist'});}
{
	node tmp = new node(pid,stat,null,null,null);
	tmp.next = plist;
	plist = tmp;
	if(stat == 1){
		rlist = insert_rll(rlist,tmp);
		}
	else{ 
		slist = insert_sll(slist,tmp);
		}
}


node insert_pll(node x, node n)
requires x::ll<R> * n::node<_@L,1@L,_@M,_@A,_@A>
ensures res::ll<R1> & R1 = union(R,{n}) & res = n;
requires x::ll<R> * n::node<_@L,v@L,_@M,_@A,_@A> & v != 1
ensures res::ll<R1> & R1 = union(R,{n}) & res = n;
{
	n.next = x;
	return n;
}

node insert_rll(node x, node n)
requires x::rll<R> * n::node<_@L,1@L,_@A,_@M,_@A>
ensures res::rll<R1> & R1 = union(R,{n}) & res = n;
{
	n.rnext = x;
	return n;
}

node insert_sll(node x, node n)
requires x::sll<R> * n::node<_@L,v@L,_@A,_@A,_@M> & v != 1
ensures res::sll<R1> & R1 = union(R,{n}) & res = n;
{
	n.snext = x;
	return n;
}

