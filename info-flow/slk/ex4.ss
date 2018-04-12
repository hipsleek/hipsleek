add(x,y) 
  requires true
  ensures S(x)<= S(res) & S(y)<= S(res);

  requires true
  ensures LUB(S(x),S(y)) <=g S(res);


   S(x)=L & S(y)=H
     &  S(x)<=S(res) & S(y)<=S(res) |- S(y)=H;

   S(x)=L & S(y)=H
     &  S(x)<=S(res) & S(y)<=S(res) |- S(y)<=H;

   S(res) = LUB(S(x),S(y))

     L <= S(res) |- S(res)<=L


     GFLOW(x,y) & LO(x) |- LO(y)


     FLOW(x,y) & FLOW(a,y) <--> GFLOW(LUB(x,a),y)
