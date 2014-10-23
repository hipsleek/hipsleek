data cell {
  int val;
}

void main(cell x, cell y)
  infer[@shape]
  requires true
  ensures true;
{
  if (x.val>0) {
    y.val=y.val+1;
  }
}
/*
# cell1.ss 

@imm error?

Checking procedure f_r_1200_while_10_2$cell~cell... Proving binding in method f_r_1200_while_10_2$cell~cell for spec  EAssume ref [x;y]
   emp&{FLOW,(4,5)=__norm}[]
   , Line 0

( []) bind: node  y'::cell<val_10_1205'>@L cannot be derived from context
cell.ss_10:9_10:14

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: []
 State:
        fe_kind: MAY
        fe_name: separation entailment
        fe_locs: {
                  fc_message: do_unmatched_rhs : y'::cell<val_10_1205'>@L
                  fc_current_lhs_flow: {FLOW,(4,11)=__MayError}}
[[ COND ==>  UnmatchedRHSData ==> ]]
 ]cell.ss_10:9_10:14


*/
