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

node set_right (node x)
infer [H,G] requires H(x) ensures G(x,res);
//requires x::tree<> ensures x::tree<> & res=x;
{
  //[1]
  //dprint;
  if (x.right==null) 
    { //[1.1]
      //dprint;
      assert true;
   	}
  else 
    { //[1.2]
      //dprint;
  		x.right =set_right(x.right);
  		x.left = set_right(x.left);
  	}
  //dprint;
  return x;
}

/*
# tll-if.ss  --sa-dnc 

[ HP_802(left_27_800) ::=UNKNOWN,

 H(x_834) ::= x_834::node<left_27_800,right_27_801>@M * HP_802(left_27_800)&right_27_801=null
   \/  x_834::node<left_27_800,right_27_801>@M * H(left_27_800) * H(right_27_801)&right_27_801!=null,

 G(x_836,res_837) ::= HP_802(left_27_800) * res_837::node<left_27_800,right_27_801>@M
                           &right_27_801=null & res_837=x_836
   \/  G(right_27_801,v_node_34_823) * G(left_27_800,v_node_35_833) * 
       res_837::node<v_node_35_833,v_node_34_823>@M&right_27_801!=null & res_837=x_836]

===========

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
