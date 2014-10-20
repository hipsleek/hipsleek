data cell {
  int val;
}

void main(cell x, cell y)
  infer[//@shape,
  @post_n]
  requires x::cell<a>*y::cell<b>
  ensures x::cell<c>*y::cell<d>;
{
    y.val=x.val+1;
}
/*
# cell2aq.ss 

This shows how post_n can be trigered after
shape analysis.

Post Inference result:
main$cell~cell
 requires x::cell<a> * y::cell<b> & MayLoop[]
     ensures x::cell<c_1211> * 
y::cell<d_1212> & a=d_1212-1 & c_1211=d_1212-1;


*/
