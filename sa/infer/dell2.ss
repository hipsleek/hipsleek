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
  infer [@shape
         ,@post_n
  ]
 requires true
  ensures true;
{
  if (y.val<x.val) {
    x.val = x.val-1;
    loop(x,y);
  }
}

/*
# dell1.ss -pcp

What happen to be base-case?

[RELDEFN post_1302: ( val_28_1231=val_28_1269 & val_28_1237<=val_28_1269) -->  post_1302(val_28_1231,val_28_1237,val_28_1269)]

void loop(cell x,cell y)
  infer [@shape
         //,@post_n
  ]

# TODO: should display the actual pre/post inferred.
*********************************************************
[ HP_11(x_1272,y_1273) ::=  x_1272::cell<val_26_1237> * y_1273::cell<val_26_1269>,
 GP_12(x_1274,y_1275) ::=  y_1275::cell<val_26_1231> * x_1274::cell<val_26_1237>]
=========================================================
*/
