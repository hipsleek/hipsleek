data cell {
  int val;
}

int main(cell x)
  infer[@shape]
  requires true
  ensures true;
{
    return x.val+1;
}
/*
# cell2b.ss --sa-dis-error

[ HP_11(x_1244,y_1245) ::=  [y_1245::cell<val_10_1236> * x_1244::cell<val_10_1241>],
 GP_12(x_1246,y_1247) ::=  [x_1246::cell<val_10_1224> * y_1247::cell<v_int_10_1238>]]

*/
