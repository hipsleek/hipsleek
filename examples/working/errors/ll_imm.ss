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


lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

// PROBLEM : no specialization
/* function to get the third element of a list */
node get_next(node x) 

/*
	requires x::lseg<r,1>
	ensures res=r;
*/
	requires x::ll<1>
	ensures res=null;

{
        dprint;
        node t = x.next;
        dprint;
        assert t'=null;
	return t;
}


/*

changed flag is NOT set properly in
 slicing.merge_mems_mx

merge_mems_nx@3@2
merge_mems_nx inp1 : (
(SLICE[self][](sat?):
   [self!=null(IN)]
   [true]
 changed flag:true
 unsat   flag:true
   alias set:[@]))
merge_mems_nx inp2 : (
(SLICE[flted_18_17][](sat?):
   [0<=flted_18_17(IN)]
   [true]
 changed flag:false
 unsat   flag:true
   alias set:[@]))
merge_mems_nx@3 EXIT out : (
(SLICE[self][](sat?):
   [self!=null(IN)]
   [true]
 changed flag:false
 unsat   flag:true
   alias set:[@]
 SLICE[flted_18_17][](sat?):
   [0<=flted_18_17(IN)]
   [true]
 changed flag:false
 unsat   flag:true
   alias set:[@]))

*/