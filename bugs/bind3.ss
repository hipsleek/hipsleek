data node{
	int val;
	node next;
}

node paper_fix (node c)
  requires c::node<_,p>
  ensures res=p;
{
      node t;
      bind c to (_,nn) in {
                dprint;
                nn=null;
                bind c to (a,b) in
                {
                  dprint;
                }
                dprint;
                t=nn;
      }
      dprint;
      return t;
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
