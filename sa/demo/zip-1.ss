data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

ltwo<p:node> == p::ll<> & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwo<r>;
   
   
HeapPred H1(node a, node b).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred G1(node a).//, node b).
HeapPred G2(node a).
 HeapPred G3(node a, node b).

node zip (node x, node y)

  infer [H1, G3]
  requires H1(x,y)
     ensures  G3(x,y);

//  requires x::ltwo<y>
//  ensures res::ll<> * y::ll<> & res=x;
{
   if (x==null) return null;
   else {
	//assume false;
     int n1=x.val;
     int n2=y.val;
     x.val = n1+n2;
     x.next = zip(x.next,y.next);
     return x;
   }
}

/*

# zip.ss

weird bug here..

 id: 10; caller: []; line: 22; classic: false; kind: POST; hec_num: 4; evars: []; infer_vars: []; c_heap: y_820::ll@M[1][Orig]
 checkentail emp&x=null & y=y_820 & x=null & v_bool_24_800' & x=null & v_bool_24_800' & 
v_null_24_781'=null & res=v_null_24_781'&{FLOW,(22,23)=__norm}[]
 |-  emp&res=x&{FLOW,(22,23)=__norm}[]. 
res:  failctx
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: failed in entailing pure formula(s) in conseq
                   fc_current_lhs_flow: {FLOW,(22,23)=__norm}}



*/

