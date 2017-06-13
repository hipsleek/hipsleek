global int context;

pred_prim sec<h:int>; 

int prop(int i)
  requires i::sec<i_sec>@L
  ensures res::sec<r_sec> & res=i & r_sec<=r_max & r_max=max(i_sec,context);

int test(int i)
  requires i::sec<i>
  ensures res::sec<_> ;
{
  int r = prop(i);
  dprint;
  /*
     (exists r_1810: i::sec<i>@M * r'::sec<r_1810>@M&
exists(r_1811:i'=r' & i=r' & context_23'=context_23 & 
              (((r_1811=r' & r_1810<=r' & context_23<=r') | 
                (r_1811=context_23 & r_1810<=context_23 & r'<context_23))))&
  */
  assert false;
  //assert/assume:ex21-hip.ss:15: 2:  : failed (must)
  return r;
}
