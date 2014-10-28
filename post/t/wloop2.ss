data cell {
  int val;
}

void main(cell x, cell y)
  infer[@post_n]
  requires x::cell<a> * y::cell<b>  
  ensures x::cell<c>*y::cell<d>; 
{
  while (y.val<x.val) 
    infer[@post_n]
    requires x::cell<a> * y::cell<b>  
    ensures x::cell<c>*y::cell<d>; 
  {
    y.val = y.val+1;
  }
}
/*
 requires emp & MayLoop[]
     ensures emp & x'=x & (((y'=x & y<x) | (y'=y & 
x<=y)));

 requires x::cell<a> * y::cell<b> & MayLoop[]
     ensures x::cell<c_1237> * 
y::cell<d_1238> & a=c_1237 & (((d_1238=c_1237 & b<c_1237) | (b=d_1238 & 
c_1237<=d_1238)));

main$int~int
 requires emp & MayLoop[]
     ensures emp & x'=x & (((y'=x & y<x) | (y'=y & 
x<=y)));

main$cell~cell
 requires x::cell<a> * y::cell<b> & MayLoop[]
     ensures x::cell<c_1225> * 
y::cell<d_1226> & a=c_1225 & (((d_1226=c_1225 & b<c_1225) | (b=d_1226 & 
c_1225<=d_1226)));

*/
