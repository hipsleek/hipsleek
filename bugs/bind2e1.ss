data node{
	int val;
	node next;
}

bool randB() 
  requires true
  ensures res or !res;

node paper_fix (node c)
  requires c::node<_,p>
  ensures c::node<_,p> & res=p;
{
      node t;
      bool b;
      bind c to (_,nn) in {
        return nn;
      }
      dprint;
      return t;
}

/*

bind node not released by exception!
  1. restore
  2. use try-catch for bind?

dprint: bind2e.ss:17: ctx:  List of Failesc Context: [FEC(0, 1, 0 )]
Escaped States:
[
 
 Try-Block:0::
 [
  Path: 
  State:emp&c=c' & 0<=0 & Anon_11=Anon_36' & nn_37'=p & nn_37'=res&{FLOW,(16,17)=__Return}[]
        es_var_measures: MayLoop
        es_trace: empty

  ]
 ]


*/
