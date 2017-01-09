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
    return new cell(0,r);
  }
  return null;
}

/*
# cell5b7.ss 

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
    return new cell(0,r);
  }
  return null;
}

This scenario should not be replaced by false; as it
would be unsound.

[ HP_12(x,y) ::=  [x::cell<val_49,DP_1251> * 
y::cell<val_87,DP_1243>],
 GP_13(x,y,res) ::=  [hfalse; 
   y::cell<val_41,DP_1243> * 
   x::cell<val_49,DP_1251>&res=null]]

Here, the relational assumption has a constructor res::cell<..>;
as shown below and the 3rd parameter of GP_13(..) is
changing.

(1;0)GP_13(x,y,r_1283) * res::cell<v_int_18_1282,r_1283>&x!=null & 
y!=null --> GP_13(x,y,res)&
true(4,5),

In this scenario, we should return:

[ HP_12(x,y) ::=  [x::cell<val_49,DP_1251> * y::cell<val_87,DP_1243>],
 GP_13(x,y,res) ::=  [GP_13(x,y,r_1283) * 
   res::cell<v_18_1282,r_1283>&x!=null & y!=null;
   y::cell<val_41,DP_1243> * 
   x::cell<val_49,DP_1251>&res=null]]

If we support a predicate split for GP_13, we will obtain two predicates

 GP_13a(x,y) ::=[GP_13a(x,y) x!=null & y!=null;
   y::cell<val_41,DP_1243> * x::cell<val_49,DP_1251>]]

 GP_13b(res) ::= [GP_13b(r_1283) * res::cell<v_18_1282,r_1283>;
   res=null]]

GP_13a now have looping left-recursion; and can have
its recursion approximated to hfalse, as follows:

   GP_13a(x,y) ::=[hfalse;
    y::cell<val_41,DP_1243> * x::cell<val_49,DP_1251>]]

On the other hand, GP_13b is just the linked-list data structure:

 GP_13b(res) ::= GP_13b(r_1283) * res::cell<v_18_1282,r_1283>
  \/ emp & res=null


*/
