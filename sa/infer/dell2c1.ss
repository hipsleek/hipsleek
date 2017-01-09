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
  infer [
         //@post_n,
    @term
  ]
  requires x::cell<a>*y::cell<b>
  ensures x::cell<aa>*y::cell<bb> & 
  (b<a & aa=b & aa=bb | b>=a & aa=a & b=bb);
{
  if (y.val<x.val) {
    x.val = x.val-1;
    loop(x,y);
  }
}

/*
# dell2c1.ss 


!!! REL POST :  post_1227(a,b,aa_1209,bb_1210)
!!! POST:  ((bb_1210=aa_1209 & b=aa_1209 & aa_1209<a) | (a=aa_1209 & b=bb_1210 &

Why so many cases? (re-check with dell2c.ss)
& why did we may MayLoop still.
Need to merge with ti3 which seems to work.

]
Termination Inference Result:
loop:  requires x::cell<a> * 
y::cell<b> & truecase {
                  a<=b -> requires emp & Term[67,1]
     ensures x::cell<aa_1209> * 
                  y::cell<bb_1210> & ((bb_1210=aa_1209 & b=aa_1209 & 
                  aa_1209<a) | (a=aa_1209 & b=bb_1210 & aa_1209<=bb_1210)); 
                  a=b+
                  2 -> requires emp & Term[67,3]
     ensures x::cell<aa_1209> * 
                  y::cell<bb_1210> & ((bb_1210=aa_1209 & b=aa_1209 & 
                  aa_1209<a) | (a=aa_1209 & b=bb_1210 & aa_1209<=bb_1210)); 
                  a=b+
                  3 -> requires emp & Term[67,4]
     ensures x::cell<aa_1209> * 
                  y::cell<bb_1210> & ((bb_1210=aa_1209 & b=aa_1209 & 
                  aa_1209<a) | (a=aa_1209 & b=bb_1210 & aa_1209<=bb_1210)); 
                  a=b+
                  4 -> requires emp & Term[67,5]
     ensures x::cell<aa_1209> * 
                  y::cell<bb_1210> & ((bb_1210=aa_1209 & b=aa_1209 & 
                  aa_1209<a) | (a=aa_1209 & b=bb_1210 & aa_1209<=bb_1210)); 
                  a=b+
                  5 -> requires emp & Term[67,6]
     ensures x::cell<aa_1209> * 
                  y::cell<bb_1210> & ((bb_1210=aa_1209 & b=aa_1209 & 
                  aa_1209<a) | (a=aa_1209 & b=bb_1210 & aa_1209<=bb_1210)); 
                  (b<=(a-7) | a=b+
                  6) -> requires emp & MayLoop[]
     ensures x::cell<aa_1209> * 
                  y::cell<bb_1210> & ((bb_1210=aa_1209 & b=aa_1209 & 
                  aa_1209<a) | (a=aa_1209 & b=bb_1210 & aa_1209<=bb_1210)); 
                  a=b+
                  1 -> requires emp & Term[67,2]
     ensures x::cell<aa_1209> * 
                  y::cell<bb_1210> & ((bb_1210=aa_1209 & b=aa_1209 & 
                  aa_1209<a) | (a=aa_1209 & b=bb_1210 & aa_1209<=bb_1210)); 
                  }




*/
