data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;



void append(node xxx, node yyyy)
  requires xxx::ll<nnn> * yyyy::ll<mmm> & nnn>0
  ensures xxx::ll<eee>& eee=nnn+mmm;
{
  // dprint;
	node tmp = xxx.next;
	/* bool fl_bb = tmp != null; */
	if (tmp!=null) {
		append(xxx.next, yyyy);
                dprint;
		return;
	}
	else {
		xxx.next = yyyy;
		return;
	}
}

/*
# append.ss

--simpl-pure-part does not make any difference to the output
even when -dd is turned on or when we use -tp oc 

What are important program variables?
 - vars in pre-conditions
 - vars of parameters
 - vars of local variables (with scope)
 - bind variables (with scope)

	/* node tmp = xxx.next; */

# ex0b.ss

Checking procedure append$node~node... 
!!! **typechecker.ml#2148:Dprint:[tmp,nnn,mmm,xxx,yyyy]
dprint(simpl): ex0b-gen-bool-append.ss:21: ctx:  List of Failesc Context: [FE

# it seems that some generated vars are not placed \
  in local vars of BLK (except v_node_20_1405)

{BLK[node tmp]((node tmp;
tmp = bind xxx to (val_17_1392,next_17_1393) [read] in 
next_17_1393);
(boolean v_bool_19_1405;
(v_bool_19_1405 = {BLK[]is_not_null___$node(tmp)};
if (v_bool_19_1405) [LABEL! 93,0: {BLK[](({BLK[node v_node_20_1402]((node v_node_20_1402;
v_node_20_1402 = bind xxx to (val_20_1397,next_20_1398) [read] in 
next_20_1398);
append$node~node(v_node_20_1402,yyyy) rec)};
dprint);
ret#)}]
else [LABEL! 93,1: {BLK[](bind xxx to (val_25_1403,next_25_1404) [write] in 
next_25_1404 = yyyy;
ret#)}]
)))}


*/
