data cell {
  int val;
}

void main(cell x, cell y)
  infer[@shape]
  requires true
  ensures true;
{
  wloop(x,y);
}
void wloop(ref cell x,ref cell y)
    infer[@shape]
    requires true
    ensures true;
{
  if (y.val<x.val) {
    y.val = y.val +1;
    wloop(x,y);
  }
}

/*
# cell5.ss 


[ HP_13(x_1290,y_1291) ::=  [
      x_1290::cell<val_17_1253> * y_1291::cell<val_17_1287>],
 GP_16(x_1292,x_1293,y_1294,y_1295) ::=  [
  emp&y_1294!=null & x_1292!=null; 
  y_1294::cell<val_17_1247> * x_1292::cell<val_17_1253>&x_1293=x_1292 
  & y_1295=y_1294]]

 Why is there an emp case for GP16?

*/
