//Ex8: null pointer dereference inside struct

/*
Proving binding in method main$ for spec  EAssume
   emp&{FLOW,(4,5)=__norm#E}[]
   struct:EBase
            emp&{FLOW,(4,5)=__norm#E}[], Line 0

( []) bind: node  tmp'::P<a_17_2020',b_17_2021'>@L&{FLOW,(1,28)=__flow#E}[] cannot be derived from context
1 File "testcases/ex8.c",Line:46,Col:11

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
 Failed States:
 [
  Label: []
  State:
    fe_kind: MAY
    fe_name: separation entailment
    fe_locs: {
        fc_message: do_unmatched_rhs : tmp'::P<a_17_2020',b_17_2021'>@L(may)
        fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}
      }
    [[ SEARCH ==>  UnmatchedRHSData]]
  ]1 File "testcases/ex8.c",Line:46,Col:11

Context of Verification Failure: _0:0_0:0

Last Proving Location: testcases/ex8.c_46:11_-1:-1
*/

struct P{
	int *a;
	int *b;
};

struct P foo(){
	struct P n;
	n.a = NULL;
	n.b = 0;
	return n;
}

int main()
{
	struct P tmp = foo();
	int x = *(tmp.a); // NULL
	int y = *(tmp.b); // NULL
	x = x + y;
	y = y + x;
	return 0;
}
