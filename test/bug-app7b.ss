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
Why isn't 24-->30 decreasing?

 es_evars: [flted_7_679; n_665]
 es_gen_impl_vars: [n_665]

Termination checking result:
(35)->(41) (ERR: not decreasing) Term[0; 0; n] -> Term[0; 0; n_665]:
Current context

pure: flted_7_697+1=flted_7_651 & flted_7_651+1=n & x'=x & y'=y & y=x & 
      0<n & tmp_36'=q_653 & tmp_36'!=null & fl_37' & tmp_36'!=null & 
      fl_37' & v_node_41_546'=q_653 & Anon_674=Anon_652 & q_675=q_653 & 
      Anon_700=Anon_698 & q_701=q_699 & flted_7_697+1+1=n_665


(35)->(41) (ERR: not decreasing) Term[0; 0; n] -> Term[0; 0; n_665]:
Current context

pure: flted_7_651+1=n & x'=x & y'=y & y=x & 0<n & tmp_36'=q_653 & 
      tmp_36'!=null & fl_37' & tmp_36'!=null & fl_37' & 
      v_node_41_546'=q_653 & Anon_674=Anon_652 & q_675=q_653 & flted_7_651+
      1=n_665

Isn't x.next supposed to decrease the rank n?
is there a bug with substitution since n=n_665 from the
verbose printing?

*/

void append(node x, node y)
  requires x::ll<n> & Term[0,n] & n>0 //x!=null //& n>0
  ensures x::lseg<y, n>;
  requires x::ll<n> & Term[0,n] & y=x  & n>0 // x!=null
  ensures x::clist<n>;
{
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append(tmp, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

