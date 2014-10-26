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
/*
  infer [@shape
         //,@post_n
  ]
  requires true ensures true;
*/
  requires x::cell<v37>*y::cell<v69>
  ensures x::cell<v37>*y::cell<v31>;
{
  if (y.val<x.val) {
    x.val = x.val-1;
    loop(x,y);
  }
}

/*
# dell1a.ss -pcp

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

   see #dell1a.ss

*/
