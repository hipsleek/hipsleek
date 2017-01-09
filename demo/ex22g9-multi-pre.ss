data cell {
  int val;
}

void pre_call(cell x)
  requires x::cell<_> ensures true;
  requires x=null ensures true;

int foo2(cell x)
  requires x!=null
  ensures res=3;
{
  pre_call(x);
  dprint;
  return 3;

}

/*
# ex22g9.ss --efa-exc 

How come there is a 
 true |-  res=3. LOCS:[0;11] (may-bug)

This should not have arisen..

Post condition cannot be derived:
  (may) cause: AndR[
1.2b: ante flow:__MayError#E conseq flow: __norm#E are incompatible flow types;
Proving precondition in method pre_call$cell(1 File "ex22g9-multi-pre.ss",Line:13,Col:2) Failed (may);
 x'!=null |-  x'=null. LOCS:[9;10;13] (may-bug),
 true |-  res=3. LOCS:[0;11] (may-bug)
]

-dd

!!! **solver.ml#7561:new_ctx: 
MaybeErr Context: 
                   fe_kind: MAY
                   fe_name: logical bug
                   fe_locs: {
                             fc_message:  true |-  res=3. LOCS:[0;11] (may-bug)
                             fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}}
[[empty]]
CEX:false

*/
