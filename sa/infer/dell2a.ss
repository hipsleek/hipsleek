data cell {
  int val;
}

/*
void main(cell x, cell y)
  infer[@shape,@post_n,@term]
  requires true
  ensures true;
{
  while (y.val<x.val) 
    infer[@shape,@post_n,@term]
      requires true
      ensures true;
  {
    x.val = x.val-1;
  }
}
*/

void loop(cell x,cell y)
  infer [@post_n
  ]
  requires x::cell<v7>*y::cell<v2>
  ensures x::cell<v7>*y::cell<v3>;
{
  if (y.val<x.val) {
    x.val = x.val-1;
    loop(x,y);
  }
}

/*
# dell2a.ss 

Why did we not detect a problem during post verification?
Why was the error below not properly highlighted?

!!! >>>>>> infer_collect_rel <<<<<<
!!! LHS and RHS Contradiction detected for:
!!! lhs: y'=y & x'=x & v2<v7 & v_bool_27_1214' & v2<v7 & v_bool_27_1214' & 
v_int_28_1269+1=v7 & val_28_1262=v7 & v7_1263=v_int_28_1269 & v2_1264=v2 & 
y!=null & x'!=null & post_1235(v3_1272,v7_1263,v7_1263,v2_1264) & 
v3_1218=v3_1272 & y'!=null & x'!=null & y'!=x'
!!! rhs: v7_1217=v7 & v7_1217=v7_1263
!!! Skip collection of following RELDEFN:
!!! rel defns:[ post_1235(v3_1218,v7_1217,v7,v2)]


This lead to a missing base-case?

[RELDEFN post_1235: ( v3_1218=v2 & v7<=v2) -->  post_1235(v3_1218,v7_1217,v7,v2)]


*/
