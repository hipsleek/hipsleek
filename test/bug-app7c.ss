data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

/*

TODO: All phase variables must be substituted. 
  We did not infer p>p as it is akin to false.
  This caused a problem during termination verification
  as the phase variables are still present.


@3! Phase Constrs:[]
@3! Inferred phase constraints:[]
@3! Phase Numbering:[]
phase_num_infer_one_scc@3
phase_num_infer_one_scc@3 EXIT out :
Checking procedure append$node~node... 
!!!Filter Label ==> Orig:2 Filtered:1
!!!Filter Label ==> Orig:2 Filtered:1
Procedure append$node~node SUCCESS

Termination checking result:
(25)->(30) (ERR: not decreasing) Term[0; p2] -> Term[0; p2]
(25)->(30) (ERR: not decreasing) Term[0; p2] -> Term[0; p2]
(25)->(30) (ERR: not decreasing) Term[0; p2] -> Term[0; p2]
(23)->(30) (ERR: not decreasing) Term[0; p1] -> Term[0; p1]

*/

void append(node x, node y)
  requires x::ll<n> * y::ll<m> & Term[n] & n>0
  ensures x::ll<e>& e=n+m;
  requires x::lseg<r, n> * r::node<b,null> & Term[n]
  ensures x::lseg<r,n> * r::node<b,y>;
{
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

