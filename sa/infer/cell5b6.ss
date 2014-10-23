data cell {
  int val;
  cell next;
}


cell wloop(cell x,cell y)
    infer[@shape]
    requires true
    ensures true;
{
  bool t = y.val<x.val;
  dprint;
  if (t) {
    y.val = y.val +1;
    cell r;
    r = wloop(x,y);
    return r;
  }
  return null;
}

/*
# cell5b6.ss 

Got:

[ HP_12(x_1291,y_1292) ::=  [x_1291::cell<val_12_1247,DP_DP_HP_1249> * 
y_1292::cell<val_12_1281,DP_DP_HP_1241>],
 GP_13(x_1305,y_1306,res_1307) ::=  [hfalse; y_1306::cell<val_12_1239,DP_DP_HP_1241> * 
x_1305::cell<val_12_1247,DP_DP_HP_1249>&res_1307=null]]


*/
