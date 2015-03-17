data node {
	int val;
	node next;
}

lseg<n,p> == self=p & n=0
  or self::node<_, q> * q::lseg<n-1,p> 
	inv n>=0;

clist<n> == self::node<_,p>*p::lseg<n-1,self>
  inv self!=null & n>0;

void append(node x, node y)
  requires x::lseg<n,null> & n!=0 & Term[n+222]
  ensures x::lseg<n,y>;
  requires x::lseg<n,null> & n!=0 & x=y & Term[n]
  ensures x::clist<n>;
{
  if (x.next!=null) append(x.next, y);
  else x.next = y;
}

/*

# ex5d-bug

  requires x::lseg<n,null> & n!=0 & Term[n+2]
  ensures x::lseg<n,y>;
  requires x::lseg<n,null> & n!=0 & x=y & Term[n]
  ensures x::clist<n>;

Above seems OK, as the two calls are in diff phases..

 Why is there is non-decreasing issue?
 Seems like another multi pre/post issue
 which occurred at Line 19?

 Why did we have Term[7,pv_1448]? What happen to n_?

Termination checking result: 
(15)->(19) (MayTerm ERR: not decreasing)  Term[7; 0; n] ->  Term[7; 1; n_1595]

id: 14; caller: []; line: 19; classic: false; kind: PRE_REC; hec_num: 1; evars: []; infer_vars: [ pv_1447,pv_1448]; c_heap: emp
 checkentail x'::node<Anon_1488,q_1489> * q_1489::lseg{}<flted_7_1487,p_1486>&
v_bool_19_1446' & q_1489!=null & n!=0 & flted_14_1490=null & y'=y & x'=x & 
p_1486=flted_14_1490 & flted_7_1487+1=n & v_node_19_1443'=q_1489 & 
Term[7,pv_1447]&{FLOW,(4,5)=__norm#E}[]
 |-  (exists flted_16_55: v_node_19_1443'::lseg{}<n_1502,flted_16_55>&
flted_16_55=null & n_1502!=0 & v_node_19_1443'=y' & Term[7,pv_1448]&
{FLOW,(4,5)=__norm#E}[]. 

*/
