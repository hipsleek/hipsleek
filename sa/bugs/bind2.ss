data node{
	int val;
	node next;
}


HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

node paper_fix (node c)
  requires c::node<_,p>
  ensures res=p;
{
      bind c to (_,nn) in {
                dprint;
                nn=null;
                //dprint;
                return nn;
      }
}

/*

ERROR : why did bind not temporarily remove a node?

[
 Label: 
 State:c::node<Anon_11,p>@M[Orig]&c=c' & Anon_11=Anon_12' & nn'=p&{FLOW,(22,23)=__norm}[]
       es_var_measures: MayLoop
       es_trace: empty

 ]

*/
