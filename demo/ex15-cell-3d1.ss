data cell{
 int fst;
}

relation P1(ann v1).
  relation P2(ann v1, ann v2).

void foo(cell c)
  requires c::cell<v>@L 
  ensures c::cell<4>@b  ;
{
 c.fst = 4;
}
/*
# ex15-cell-3d1.ss

Old system before error_infer

Checking procedure foo$cell... Proving binding in method foo$cell for spec  EAssume 
   (exists flted_10_1455,b_1456: c::cell<flted_10_1455>@b_1456&
   flted_10_1455=4&{FLOW,(4,5)=__norm#E}[]
   , Line 0

( []) bind: node  c'::cell<fst_12_1448'> cannot be derived from context
1 File "../sl_clean/imm/inf/cell-3d1.ss",Line:12,Col:1

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: []
 State:
        fe_kind: MUST
        fe_name: separation entailment
        fe_locs: {
                  fc_message: Imm annotation mismatches
                  fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}}
[[ SEARCH ==>  Match(c,c') ==> ]]
 ]1 File "../sl_clean/imm/inf/cell-3d1.ss",Line:12,Col:1

Context of Verification Failure: _0:0_0:0

Last Proving Location: ../sl_clean/imm/inf/cell-3d1.ss_12:1_12:6

Procedure foo$cell FAIL.(2)


Exception Failure("bind failure exception") Occurred!



*/
