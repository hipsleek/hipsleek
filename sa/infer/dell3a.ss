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
  infer [@post_n,@term
  ]
  requires x::cell<a>*y::cell<b>
  ensures x::cell<d>*y::cell<e>;
{
  if (y.val<x.val) {
    //dprint;
    x.val = x.val-1;
    // dprint;
    loop(x,y);
  }
}

/*
# dell3a.ss 

void loop(cell x,cell y)
  infer [@post_n
  ]

Why is this correect but not dell3.ss?

[RELDEFN post_1460: ( post_1460(d_1442,e_1443,a_1488,b) & a=1+a_1488 & b<=a_1488) -->  post_1460(d_1442,e_1443,a,b),
RELDEFN post_1460: ( d_1442=a & e_1443=b & a<=b) -->  post_1460(d_1442,e_1443,a,b)]
*************************************

!!! >>>>>> compute_fixpoint <<<<<<
!!! Input of fixcalc: post_1460:={[a,b] -> [d_1442,e_1443] -> []: (((d_1442=a && e_1443=b) && a<=b) || ( (exists (a_1488:(a_1488+1=a && post_1460(a_1488,b,d_1442,e_1443))))  && b<a))
};
bottomupgen([post_1460], [2], SimHeur);
*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1460(a,b,d_1442,e_1443), ((e_1443=d_1442 & b=d_1442 & d_1442<a) | (a=d_1442 & b=e_1443 & 
d_1442<=e_1443)), true, true)]
*************************************


*/
