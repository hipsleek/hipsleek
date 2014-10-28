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
    //dprint;
    x.val = x.val-1;
    // dprint;
    loop(x,y);
  }
}

/*
# dell1.ss -pcp

void loop(cell x,cell y)
  infer [@shape
         //,@post_n
  ]

# TODO: should display the actual pre/post inferred.
*********************************************************
[ HP_11(x2,y3) ::=  x2::cell<val37> * y3::cell<val69>,
 GP_12(x4,y5) ::=  y5::cell<val31> * x4::cell<val37>]
=========================================================

Is it true to val37 is unchanged? The spec 
inferred seems wrong

# TODO: should display the actual pre/post inferred.
*********************************************************
[ HP_11(x2,y3) ::=  x2::cell<val37> * y3::cell<val69>,
 GP_12(x4,y5) ::=  y5::cell<val31> * x4::cell<val37>]
=========================================================

Is it true to val37 is unchanged? The spec 
inferred seems wrong

   see #dell1a.ss

*/
