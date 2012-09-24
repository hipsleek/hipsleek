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
	or self::node<_@L,v@L,_@A,_@A,p> * p::sll<Rp> & R = union(Rp,{self}) & v = 2
	inv true
    mem R->(node<@L,@L,@A,@A,@M>);
    
void insert_process(int pid, int stat, ref node plist, ref node rlist, ref node slist)
case {
stat = 1 -> requires (plist::ll<R> & rlist::rll<R1> * slist::sll<R2>) & R = union(R1,R2)
	    ensures (plist::ll<R> & rlist::rll<R1> * slist::sll<R2> * plist'::node<pid@L,v@L,plist@M,rlist@A,_@M> 
	    	* rlist'::node<pid@A,v@A,plist@A,rlist@A,_@A>) & plist' = rlist' & R = union(R1,R2) & v = 1;
stat != 1 -> requires (plist::ll<R> & rlist::rll<R1> * slist::sll<R2>) & R = union(R1,R2)
	    ensures (plist::ll<R> & rlist::rll<R1> * slist::sll<R2> * plist'::node<pid@L,v@L,plist@A,_@A,slist@A>
	    	* slist'::node<pid@A,v@A,plist@A,_@A,slist@A>) & plist' = slist' & R = union(R1,R2) & v != 1;}
{
	node tmp = new node(pid,stat,null,null,null);
	tmp.next = plist;
	if(stat == 1){
		rlist = insert_rll(rlist,tmp);
		}
	else{
		slist = insert_sll(slist,tmp);
		}
	plist = tmp;
}

node insert_pll(node x, ref node n)
requires x::ll<R> * n::node<_@L,_@L,_@M,_@M,_@M>
ensures n::node<_@L,_@L,x@A,_@M,_@M> * x::ll<R>;
{
	n.next = x;
	return n;
}

node insert_rll(node x, ref node n)
requires x::rll<R> * n::node<_@L,_@L,_@A,_@M,_@A>
ensures n::node<_@L,_@L,_@A,x@A,_@A> * x::rll<R>;
{
	n.rnext = x;
	return n;
}

node insert_sll(node x, ref node n)
requires x::sll<R> * n::node<_@L,_@L,_@A,_@A,_@M>
ensures n::node<_@L,_@L,_@A,_@A,x@A> * x::sll<R>;
{
	n.snext = x;
	return n;
}

