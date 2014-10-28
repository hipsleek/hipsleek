data cell {
  int val;
}

void wloop(cell x,cell y)
    infer[@shape]
    requires true
    ensures true;
{
  bool t = y.val<x.val;
  y.val = y.val +1;
  wloop(x,y);
  // dprint;
}

/*
# cell5b2.ss 

void wloop(cell x,cell y)
    infer[@shape]
    requires true
    ensures true;
{
  bool t = y.val<x.val;
  y.val = y.val +1;
  wloop(x,y);
  dprint;
}

Got:

 (0)GP_12(x,y)&x!=null & y!=null --> GP_12(x,y)& true(4,5)

Two issues : 

 (1) Got  true(4,5). Isn't it norm flow?
 (2) Why did we not get false post-condition?

*********************************************************
*******relational definition (flow= (4,5))********
*********************************************************
[ HP_11(x_1280,y_1281) ::=  [x_1280::cell<val_10_1237> * y_1281::cell<val_10_1277>],
 GP_12(x_1282,y_1283) ::=  [emp&y_1283!=null & x_1282!=null]]
*************************************


*/
