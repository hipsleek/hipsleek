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
         //,@term
  ]
  requires x::cell<a>*y::cell<b>
  ensures x::cell<aa>*y::cell<bb>;
{
  if (y.val<x.val) {
    x.val = x.val-1;
    loop(x,y);
  }
}

/*
# dell2b.ss 

[( post_1226(a,b,aa_1208,bb_1209), ((bb_1209=aa_1208 & b=aa_1208 & aa_1208<a) | (a=aa_1208 & b=bb_1209 & 
aa_1208<=bb_1209)), true, true)]
*************************************

!!! REL POST :  post_1226(a,b,aa_1208,bb_1209)
!!! POST:  ((bb_1209=aa_1208 & b=aa_1208 & aa_1208<a) | (a=aa_1208 & b=bb_1209 &

 requires x::cell<a> * 
y::cell<b> & MayLoop[]
     ensures x::cell<aa_1208> * 
y::cell<bb_1209> & ((bb_1209=aa_1208 & b=aa_1208 & aa_1208<a) | (a=aa_1208 & 
b=bb_1209 & aa_1208<=bb_1209));


*/
