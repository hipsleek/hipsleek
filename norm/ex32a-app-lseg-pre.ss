/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

/* view for a singly linked list */

lseg<p> == self = p 
      or self::node<_, q> * q::lseg<p> & self!=p
  inv true;

	
	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

HeapPred H(node x, node@NI y).

void append3(node x, node y)
/*
  infer [@shape_pre,@classic]
  requires true
  ensures true;
  infer[@classic]
  requires x::lseg<null> & x!=null
  ensures true;
*/

  infer [H,@classic]
  requires H(x,y)
  ensures true;

{    
	if (x.next == null) 
           x.next = y;
	else
           append3(x.next, y);
}
/*
# ex32a,ss

void append3(node x, node y)
  infer [H,@classic]
  requires H(x,y)
  ensures true;

{    
	if (x.next == null) 
           x.next = y;
	else
           append3(x.next, y);
}

[ // BIND
(0)H(x,y@NI)&
true --> x::node<val_36_1569,next_36_1570>@M * 
         HP_1571(next_36_1570,y@NI,x@NI)&
true,
 // PRE_REC
(2;0)HP_1571(next_36_1570,y@NI,x@NI)&
next_36_1570!=null |#| x::node<val_36_1569,next_36_1570>@M&
true --> H(next_36_1570,y@NI)&
true,
 // POST
(1;0)HP_1571(next_36_1570,y@NI,x@NI)&
y'=y & x'=x & next_36_1570=null & next_37_1580=next_36_1570 --> emp&
true]

--new-pred-synthesis  (default)

# Why can't we infer:

   requires x::lseg<null> & x!=null
   ensures true;

!!! **WARNING****syn.ml#188:Merging is not performed due to the set of pre-hprels does not have identical LHS and/or guards
!!! **iast.ml#3923:Adding the view H into iprog.
Context of Verification Failure: ex32a-app-lseg-pre.ss_34:10_34:14

Last Proving Location: ex32a-app-lseg-pre.ss_39:11_39:29

ERROR: at _0:0_0:0
Message: HP_1571 is neither 2 a data nor view name

!!! **synUtils.ml#792:Failure("HP_1571 is neither 2 a data nor view name")
!!! **synUtils.ml#793:WARNING: Cannot normalize the view H
!!! **syn.ml#686:XXX Scheduling pred_elim_useless
!!! **norm.ml#165:USELESS Parameters eliminated:[]
!!! **syn.ml#689:XXX Scheduling pred_reuse
!!! **syn.ml#690:XXX derived_view names:[]
!!! **syn.ml#693:XXX existing view names:[memLoc,H,ll]
!!! **syn.ml#695:XXX reuse found ...:[]
!!! **syn.ml#696:XXX Scheduling pred_reuse_subs
!!! **sa3.ml#3289:DERIVED VIEWS:[]
!!! **cf_ext.ml#81:add_data_tags_to_obj

--ops (wrong..)

[ H(x_1600,y_1601) ::= x_1600::node<val_36_1569,next_36_1570>@M&next_36_1570=null(4,5)]


*/
