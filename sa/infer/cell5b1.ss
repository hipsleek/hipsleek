data cell {
  int val;
}

void wloop(cell x,cell y)
    infer[@shape]
    requires true
    ensures true;
{
  bool t = y.val<x.val;
  dprint;
  if (t) {
    y.val = y.val +1;
    wloop(x,y);
  }
  dprint;
}

/*
# cell5b1.ss 

Got:

 // POST
(1;0)GP_12(x,y)&x!=null & y!=null --> GP_12(x,y)&
true(4,5),
 // POST
(2;0)y::cell<val_10_1231> * x::cell<val_10_1237>&true --> GP_12(x,y)&
true(4,5)]

The inferred spec seems incorrect correct.

 GP_12(x_1276,y_1277) ::=  [emp&y_1277!=null & x_1276!=null; 
  y_1277::cell<val_10_1231> * x_1276::cell<val_10_1237>]]

The fix-point seems to have approximated GP_12(x,y) to true 
rather than false. I guess we need to correct this 
fix-point process.

The missing step seems to be a fixpoint operation,
where GP_12(..) is first approximated to false. We can trigger this
when GP_12 is not linear-recursive. This would later result
in the following:

 GP_12(x_1276,y_1277) ::=  [y_1277::cell<val_10_1231> 
   * x_1276::cell<val_10_1237>]]

[ // BIND
(0)HP_11(x,y)&true --> y::cell<val_10_1231> * HP_1232(x,y@NI)&
true(4,5),
 // BIND
(0)HP_1232(x,y@NI)&true --> x::cell<val_10_1237>&
true(4,5),
 // PRE_REC
(1;0)x::cell<val_10_1237> * y'::cell<v_int_13_1263>&true --> HP_11(x,y')&
true(4,5),
 // POST
(1;0)GP_12(x,y)&x!=null & y!=null --> GP_12(x,y)&
true(4,5),
 // POST
(2;0)y::cell<val_10_1231> * x::cell<val_10_1237>&true --> GP_12(x,y)&
true(4,5)]


*/
