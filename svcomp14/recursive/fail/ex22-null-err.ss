data cell {
  int val;
}

int null_err()
  requires true
  ensures true & flow __Error;
{
  cell x;
  x =null;
  return x.val;
}

/*
# ex22-null-err.ss

Error verified successfully.

WARNING: ex22-null-err.ss_7:10_7:29:the result type __Error#E is not covered by the throw list[__norm#E]

If we replace with ensures true in ex22a.ss; we got the
error below. Is this detected at post?

( []) bind: node  x_37'::cell<val_11_1347'>@L cannot be derived from context
ex22-null-err.ss_11:9_11:14

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: []
 State:
        fe_kind: MUST
        fe_name: separation entailment
        fe_locs: {
                  fc_message: do_unmatched_rhs : x_37'::cell<val_11_1347'>@L
                  fc_current_lhs_flow: {FLOW,(6,10)=__Error#E}}
[[ COND ==>  UnmatchedRHSData ==> ]]
 ]ex22-null-err.ss_11:9_11:14

Context of Verification Failure: 1 File "",Line:0,Col:0

Last Proving Location: 1 File "ex22-null-err.ss",Line:11,Col:9

Procedure null_err$ FAIL.(2)

Exception Failure("bind failure exception") Occurred!

*/
