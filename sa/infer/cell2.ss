data cell {
  int val;
}

void main(cell x, cell y)
  infer[@shape]
  requires true
  ensures true;
{
    y.val=y.val+1;
}
/*
# cell2.ss --sa-dis-error

!!! shape inference for flow:(4,5)
*********************************************************
*******relational definition (flow= (4,5))********
*********************************************************
[ HP_11(x_1237,y_1238) ::=  [y_1238::cell<val_10_1224>],
 GP_12(x_1239,y_1240) ::=  [y_1240::cell<v_int_10_1236>]]


*/
