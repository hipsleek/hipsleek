data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2,int v,int r).
  relation P3(ann v1,ann v2).

int foo(cell c)
/*
  requires c::cell<v>@L
  ensures res=v;
*/
  infer [P3]
  requires c::cell<v>@a 
  ensures c::cell<v>@b & res=v & P3(a,b);
{
 int x = c.fst;
 return x;
}
/*
# ex3d5b.ss

Checking procedure foo$cell... Exception(look_up_view_def_raw):Not_found
#####infer_pure_m_x 1
Exception(check_exp1):Error.Ppf(_)
Exception(check_exp):Error.Ppf(_)
Exception(check Assign (rhs)):Error.Ppf(_)
Exception(check_exp1):Error.Ppf(_)
Exception(check_exp):Error.Ppf(_)
Exception(check_exp1):Error.Ppf(_)
Exception(check_exp):Error.Ppf(_)
Exception(check_exp1):Error.Ppf(_)
Exception(check_exp):Error.Ppf(_)
Exception(check_exp1):Error.Ppf(_)
Exception(check_exp):Error.Ppf(_)
Proving binding in method foo$cell for spec  EAssume 
   (exists v_1464,b_1465: c::cell<v_1464>@b_1465&res=v & P3(a,b_1465) & 
   v_1464=v&{FLOW,(4,5)=__norm#E}[]
   , Line 0

( []) bind: node  c'::cell<fst_18_1457'>@L cannot be derived from context
1 File "ex3d5b-cell-inf-L-post-only.ss",Line:18,Col:9

(Cause of Bind Failure) List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: []
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message:  true |-  a<:@L. LOCS:[0] (may-bug)
                  fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}}
[[ SEARCH ==>  Match(c,c') ==> ]]
 ]1 File "ex3d5b-cell-inf-L-post-only.ss",Line:18,Col:9

Context of Verification Failure: _0:0_0:0

Last Proving Location: ex3d5b-cell-inf-L-post-only.ss_18:9_18:14
Exception(check_specs_infer):Failure("bind failure exception")
Exception(check_proc):Failure("bind failure exception")

Procedure foo$cell FAIL.(2)


Exception Failure("bind failure exception") Occurred!


*/
