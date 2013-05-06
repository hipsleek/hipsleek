data node {
	int val; 
	node next;
	node parent;
	node left;
	node right;	
}

tree<p,S> == case {
  S={} -> [] self=null & S = {};
  S!={} -> [] self::node<_,_@A,p,l,r> * l::tree<self,Sl> * r::tree<self,Sr> & S = union(Sl,Sr,{self})
  & self!=p & p notin Sl & p notin Sr;}
  inv (self=null & S={} | self!=null & self in S) & p notin S
		memE S->(node<@L,@A,@M,@M,@M>);

treeseg<p,ph,h,S> == case {
  self = h -> [] S = {}  & p=ph; 
  self!=h -> [] self::node<_@L,_@A,p,l,r> * l::treeseg<self,ph,h,Sl> * r::tree<self,Sr> 
      & h notin Sr & h notin Sl 
  & S = union(Sl,Sr,{self}) & p!=ph & p notin Sr & p notin Sl & self!=p & (ph=self | ph in Sl)
  or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::treeseg<self,ph,h,Sr>  & h notin Sl & h notin Sr
  & S = union(Sl,Sr,{self}) & p!=ph & p notin Sr & p notin Sl & self!=p & (ph=self | ph in Sr); }
  inv h notin S & p notin S  
  & (self=h & S={} | self!=h & self in S)
  & (p=ph & S={} | ph!=p & ph in S)
       memE S->(node<@L,@A,@M,@M,@M>);	
 			
// proven successfully
lemma self::tree<p,S> <- self::treeseg<p,ph,h,S1> * h::tree<ph,S2> & S = union(S1,S2); 

void tree_remove(node x, ref node q1t)
requires q1t::tree<_,S> * x::node<_,_@A,_,_,_> 
ensures q1t'::tree<_,S1> & S = union(S1,{x});
//requires q1t::tree<p,S> * x::node<_,_@A,px,_,_>
//ensures q1t'::treeseg<p,px,x,S1> * px::tree<_,S2> & S = union(S1,S2,{x});
{
if (q1t == null) return;
else if (x.val < q1t.val) tree_remove(x,q1t.left);
else if(x.val > q1t.val) tree_remove(x,q1t.right);
else {
	node temp;
	if (q1t.left == null){
		temp = q1t.right;
		q1t.right = null;
		q1t = temp;
	}
	else if(q1t.right == null) {
		temp = q1t.left;
		q1t.left = null;
		q1t = temp;
	}
	else {
		temp = q1t.left;
		q1t.val = temp.val;
		tree_remove(temp,q1t.left);
	}
    }
dprint;
}

/*
void tree_remove_using_parent(node x, ref node q1t)
requires q1t::tree<p,S> & x in S
ensures q1t'::tree<p,S1> & S = union(S1,{x});
{ 
  if (x == q1t) 
  { 
	node qp = q1t.parent;
	node qr = q1t.right;
	node ql = q1t.left;
	if (qp == null) q1t = null;
	else if (ql == null && qr == null)
		if (qp.left == q1t) { 
			qp.left = null;
			qp = null;
		}
		else { qp.right = null;
			qp = null;
		}
	else if (ql == null && qr != null) {
		if (qp.left == q1t) { 
			qp.left = qr;
			qr.parent = qp;
			qp = null;
			qr = null;
		}
		else { qp.right = qr;
			qr.parent = qp;
			qp = null;
			qr = null;
		}
	}
	else if (qr == null && ql != null) {
			if (qp.left == q1t) { 
			qp.left = ql;
			ql.parent = qp;
			qp = null;
			ql = null;
		}
		else { qp.right = ql;
			ql.parent = qp;
			qp = null;
			ql = null;
		}
	}
	else { q1t.val = ql.val;
		tree_remove(ql,q1t);
	}
	
  }
  else if (x.val <= q1t.val) {
	  tree_remove(x,q1t.left);
	}
	else tree_remove(x,q1t.right);
}
*/
