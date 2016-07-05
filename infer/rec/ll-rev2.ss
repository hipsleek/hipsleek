/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/*
TODO : two problems:
(a)  wrong message
(b) bad relation formed.

ERROR: at _0_0 
Message: compute_fixpoint#fixcalc.ml: fails as it requires a
        fixpoint calculator to be located at /usr/local/bin/fixcalc_mod
 
FIXPOINT:  exists(xs:(t_573=0 & t=0 | 1<=t & t_573=t) & -1<=m & 1<=n & 
A(xs',t_573,m_551,n_550) & xs!=null & -1+m_551=m & 1+n_550=n) | (m=0 & t=0 | 
1<=t & m=t) & n=0 & xs'=null

NEW RELS: [ ( exists(xs:(t_573=0 & t=0 | 1<=t & t_573=t) & -1<=m & 1<=n & 
A(xs',t_573,m_551,n_550) & xs!=null & -1+m_551=m & 1+n_550=n)) -->  A(xs',t,m,n), ( (m=0 & t=0 | 1<=t & m=t) & n=0 & xs'=null) -->  A(xs',t,m,n)]
*/
	
	
relation A(int x, int y, int z).

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
        infer [A]
	requires xs::ll<n> * ys::ll<m> 
	ensures ys'::ll<t> & A(m,n,t) & xs'=null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
    //dprint;
		xs.next = ys;
		ys = xs;
		xs = tmp;
    //dprint;
		reverse(xs, ys);
	}
}
