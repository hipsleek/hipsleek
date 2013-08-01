data cell{
	int val;
}

//ll<> == self = null  or self::node<_, q> * q::ll<>;

HeapPred H1(cell a, cell b).
HeapPred G1(cell a, cell b).

int sum (cell x, cell y)
  infer [H1,G1]
  requires H1(x,y)
  ensures  G1(x,y);
/*
  requires x::cell<a>*y::cell<b>
  ensures x::cell<a>*y::cell<b> & res=a+b;
*/
{
   int n1 = x.val;
   int n2 = y.val;
   return n1+n2;
}

/*
Obtained:

[ H1(x,y)&true --> x::cell<val_19_781>@M&true]

GOT a failure, but it still proceeded to do shape inference!
This is a little confusing. Also, why is this a must error?

(Cause of Bind Failure):pair.ss:20: 12:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        fe_kind: MUST
        fe_name: separation entailment
        fe_locs: {
                  fc_message: infer_heap_node
                  fc_current_lhs_flow: {FLOW,(22,23)=__norm}}
 ]


*/

