data cell {
  int val;
}

HeapPred H1(cell a, cell c).
HeapPred G1(cell a, cell b).

void wloop(cell x,cell y)
/*
    infer[@shape]
    requires true
    ensures true;
*/
  infer [H1,G1] requires H1(x,y) ensures G1(x,y);
//  requires x::cell<3>*y::cell<3> ensures x::cell<3>*y::cell<3>;
{
  //dprint;
  if (y.val<x.val) {
    y.val = y.val +1;
    wloop(x,y);
  }
  // dprint;
}

/*
# cell5b.ss 

  if (y.val<x.val) {
    y.val = y.val +1;
    wloop(x,y);
  }

 Why is there an emp case for GP_12?

 What happens to the x,y nodes?

 // POST
(1;0)GP_12(x,y)&x!=null & y!=null --> GP_12(x,y)&
true(4,5),
 // POST
(2;0)y::cell<val_10_1231> * x::cell<val_10_1237>&true --> GP_12(x,y)&
true(4,5)]

--esl

id: 15; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ HP_11,GP_12,HP_1232]; c_heap: emp
 checkentail GP_12(x',y')&y'=y & x'=x & val_10_1231<val_10_1237 & v_bool_10_1209' & 
val_10_1231<val_10_1237 & v_bool_10_1209' & v_int_11_1263=1+val_10_1231 & 
val_11_1258=val_10_1231 & x!=null & y'!=null&{FLOW,(4,5)=__norm}[]
 |-  GP_12(x,y)&{FLOW,(4,5)=__norm}[]. 


[ HP_11(x_1272,y_1273) ::=  [x_1272::cell<val_10_1237> * y_1273::cell<val_10_1269>],
 GP_12(x_1274,y_1275) ::=  [emp&y_1275!=null & x_1274!=null; y_1275::cell<val_10_1231> * 
x_1274::cell<val_10_1237>]]



*/
