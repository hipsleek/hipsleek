HeapPred HP_1007(node y, node@NI x).
HeapPred HP_1008(node next_30_934, node@NI y).
HeapPred HP_1015(node next_30_942, node@NI x).
HeapPred HP_1309(node y, int n).
HeapPred HP_1312(node y, int n).
HeapPred HP_2399(node y, int n).
HeapPred HP_2402(node y, int n).
HeapPred HP_2405(node y, int n).

zip:SUCCESS[
ass [H,G][]:{
  // BIND (2;0)
  H(x,y)&x!=null --> x::node<val,next>@M * HP_1007(next,y) * HP_1008(y,x);
 // BIND (2;0)
  HP_1008(y,x)&true --> y::node<val,next>@M * HP_1015(next,x);
 // PRE_REC (2;0)
  HP_1007(next,y) * HP_1015(next1,x)&true --> H(next,next1);
 // POST (1;1;0)
  H(res,y)&y=null & x=null & res=null & res=x --> G(x,y,res);
 // POST(2;0)
 x::node<val,next>@M * G(next,next1,v1) * y::node<val1,next1>@M *
  res::node<v,v1>@M&true --> G(x,y,res)
 }

hpdefs [H,G][]:{
  H(x,y) <-> HP_1309(x,n) * HP_1312(y,n1)&n=n1;
  G(x,y,res) <-> HP_2399(x,n) * HP_2402(y,n1) * HP_2405(res,n2)&((n<=0 & n1<=0 & 1<=n2) |
   (n1<=0 & n2<=0 & 1<=n) | (n=n2 & n<=n1 & 1<=n) | (n<=0 & n2<=0) | (n=n1 &1<=n & n<n2) | (n1=n2 & 1<=n1 & n1<n));
 HP_1309(x,n) <->
  x::node<val,next>@M * HP_1309(next,n_1310)&n=1+n_1310 & 0<=n_1310
   or emp&x=null & n=0 ;
 HP_1312(y,n) <->
  y::node<val,next>@M * HP_1312(next,n_1313)&n=1+n_1313 & 0<=n_1313
   or emp&y=null & n=0;
 HP_2399(x,n) <->
   x::node<val,next>@M * HP_2399(next,n_2400)&n=1+n_2400 & 0<=n_2400
    or emp&x=null & n=0;
 HP_2402(y,n) <->
  y::node<val,next>@M * HP_2402(next,n_2403)&n=1+n_2403 & 0<=n_2403
   or emp&y=null & n=0;
 HP_2405(res,n) <->
  res::node<v1,v>@M * HP_2405(v,n_2406)&n=1+n_2406 & 0<=n_2406
   or emp&res=null & n=0
 }
]
