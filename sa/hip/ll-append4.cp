ass []:{  	HP1(a,x) * x::node<_,y>&a=null -> G2(x,y) ,
		H1(x)->  x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H1(a),
		x::node<_,b> * G2(b,y)&b!=null -> G2(x,y)}

hp_defs [H1, G2]:{ 	
		H1(x) ->  x::node<val_96_617,next_96_618> * HP_619(next_96_618),
HP_619(next_96_618)->  
 emp&next_96_618=null
 or next_96_618::node<val_96_617,next_96_622> * HP_619(next_96_622),
G2(x,y)->  x::node<val_96_610,y_611> * HP_612(y_611,y)&true,
HP_612(y_611,y)->  
 emp&y_611=y
 or y_611::node<val_96_610,y_615> * HP_612(y_615,y)&y_611!=null
 }


/*
HP_RELDEFN HP_580:  HP_580(v_node_96_597)::  
 v_node_96_597::node<val_96_617,next_96_618> * HP_619(next_96_618)&true
 or v_node_96_597::node<val_96_561',next_96_562'> * 
    next_96_562'::node<val_96_617,next_96_618> * HP_619(next_96_618)&true
 or emp&v_node_96_597=null
 ,
HP_RELDEFN G2:  G2(x,y)::  x::node<val_96_610,y_611> * HP_612(y_611,y)&true,
HP_RELDEFN H1:  H1(x)::  x::node<val_96_617,next_96_618> * HP_619(next_96_618)&true,
HP_RELDEFN HP_612:  HP_612(y_611,y)::  
 emp&y_611=y
 or y_611::node<val_96_610,y_615> * HP_612(y_615,y)&y_611!=null
 ,
HP_RELDEFN HP_619:  HP_619(next_96_618)::  
 emp&next_96_618=null
 or next_96_618::node<val_96_617,next_96_622> * HP_619(next_96_622)&true


*/
