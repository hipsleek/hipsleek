data node2{
	node2 n;
	node2 s;
}

//skipll<> == self=null 	or	self::node2<p,q> * q::skipll<> * p::lseg<q>;

lseg<q> ==  self=q 	
   or	self::node2<n,null>* n::lseg<q>
inv true;

ll<> ==  self=null 	
   or	self::node2<n,null>* n::ll<>
inv true;

	
HeapPred SLL(node2 a).
HeapPred SLSEG(node2 a,node2@NI b).
HeapPred SLSEGP(node2 a,node2@NI b).

/*
bool skip1(node2 l)
infer[SLL] requires SLL(l) ensures true;
//requires l::skipll<> ensures res;

{
	if (l==null) return true;
	else return skip1(l.s) && skip0(l.n,l.s);
}
*/

bool skipt(node2 l) 
 infer[SLL] requires SLL(l) ensures res;// res
//requires l::ll<> ensures l::ll<> & res;
{
	if (l == null) return true;
	else  {
          if (l.s==null) return skipt(l.n);
          else return false;
        }
}

/*
 id: 20; caller: []; line: 33; classic: false; kind: POST; hec_num: 2; evars: []; infer_vars: [SLL,HP_811,HP_812]; c_heap: emp
 checkentail HP_811(n_38_809) * HP_812(s_38_810) * l::node2<n_38_809,s_38_810>@M[Orig]&
l!=null & !(v_bool_36_785') & l!=null & !(v_bool_36_785') & s_38_810!=null & 
!(v_bool_38_784') & s_38_810!=null & !(v_bool_38_784') & 
!(v_boolean_39_783') & res=v_boolean_39_783'&{FLOW,(22,23)=__norm}[]
 |-  emp&res&{FLOW,(22,23)=__norm}[]. 
res:  failctx
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: failed in entailing pure formula(s) in conseq
                   fc_current_lhs_flow: {FLOW,(22,23)=__norm}}
*/
