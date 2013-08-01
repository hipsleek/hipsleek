// simpler tll working example

data node{
	node left;
	node right;
}

/* predicate for a non-empty tree with chained leaf list */

/* predicate for a non-empty tree  */
 tree<> == self::node<_,null>
	or self::node<l,r> * l::tree<> * r::tree<>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node a).
PostPred G(node a, node c).

  bool rand() 
  requires true
  ensures res or !res;

node set_right (node x)
//infer [H,G] requires H(x) ensures G(x,res);
requires x::tree<> ensures x::tree<> & res=x;
{
  //[1]
  if (x.right==null) 
    { //[1.1]
      assert true;
   	}
  else 
    { //[1.2]
  		x.right =set_right(x.right);
  		x.left = set_right(x.left);
     }
  if (rand()) {
    assert true;
  }
  else {
    assert true;
  }
  dprint;
  return x;
}

/*
# tll-if-2.ss

Entail_Stack now logs cond_path to track the
state for conditionals.
  - 0 initially
  - 1 then brach
  - 2 else branch
Note that the path is stored in reverse
   es_cond_path: [2; 1; 0]


Successful States:
[
 Label: [(,0 ); (,1 ); (,0 ); (,1 )]
 State:x'::node<Anon_819,flted_11_818>@M[Orig]&flted_11_818=null & x=x' & flted_11_818=null & v_bool_30_783' & flted_11_818=null & v_bool_30_783' & v_bool_39_786' & v_bool_39_786'&{FLOW,(22,23)=__norm}[]
       es_var_measures 2: MayLoop
       es_trace: empty
       es_cond_path: [1; 1; 0]
;
 Label: [(,1 ); (,2 ); (,0 ); (,1 )]
 State:x'::node<Anon_819,flted_11_818>@M[Orig]&flted_11_818=null & x=x' & flted_11_818=null & v_bool_30_783' & flted_11_818=null & v_bool_30_783' & !(v_bool_39_786') & !(v_bool_39_786')&{FLOW,(22,23)=__norm}[]
       es_var_measures 2: MayLoop
       es_trace: empty
       es_cond_path: [2; 1; 0]
;
 Label: [(,0 ); (,1 ); (,1 ); (,2 )]
 State:r_824::tree@M[0][Orig][LHSCase] * l_823::tree@M[0][Orig][LHSCase] * x'::node<l_823,r_824>@M[Orig]&x=x' & r_824!=null & !(v_bool_30_783') & r_824!=null & !(v_bool_30_783') & r_824!=null & r_824!=null & r_824=right_36_841 & l_823!=null & l_823!=null & l_823=left_37_851 & v_bool_39_786' & v_bool_39_786'&{FLOW,(22,23)=__norm}[]
       es_var_measures 2: MayLoop
       es_trace: empty
       es_cond_path: [1; 2; 0]
;
 Label: [(,1 ); (,2 ); (,1 ); (,2 )]
 State:r_824::tree@M[0][Orig][LHSCase] * l_823::tree@M[0][Orig][LHSCase] * x'::node<l_823,r_824>@M[Orig]&x=x' & r_824!=null & !(v_bool_30_783') & r_824!=null & !(v_bool_30_783') & r_824!=null & r_824!=null & r_824=right_36_841 & l_823!=null & l_823!=null & l_823=left_37_851 & !(v_bool_39_786') & !(v_bool_39_786')&{FLOW,(22,23)=__norm}[]
       es_var_measures 2: MayLoop
       es_trace: empty
       es_cond_path: [2; 2; 0]

 ]



# tll-if.ss


 //[1]
 H(x) --> x::node<left_25_800,right_25_801>@M * H_2(left_25_800) 
  * H_3(right_25_801).
 //[1.2]
 H_3(right_25_801)&right_25_801!=null --> H(right_25_801).
 //[1.2]
 H_2(left_25_800) --> H(left_25_800).
 //[1.1]
 H_3(right_25_801)&right_25_801=null --> emp.

========


 //(4)
 G(right_25_801,v_node_31_823) * G(left_25_800,v_node_32_833) * 
  x::node<v_node_32_833,v_node_31_823>@M&right_25_801!=null & 
  res=x --> G(x,res).
 //(6)
 H_2(left_25_800) * x::node<left_25_800,right_25_801>@M&res=x & 
  right_25_801=null --> G(x,res).




*/
