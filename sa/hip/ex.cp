constrs:{ H(x)&true -> x::node<val_24_5410,next_24_5420> * HP_557(next_24_5420,x)&true,
 HP_557(tmp_190,x) * x::node<val_24_566,next_25_5450>&
v_node_26_5460=tmp_190 & next_25_5450=null -> G(x,v_node_26_5460)&true}


constrs_traverse:{ HP_535(x0,x) * x::node<val_17_543,x0>&x0!=null -> H(x0),
x::node<val_17_543,x_552> * G(x_552,x0)&x_552!=null -> G(x,x0),
H(x) -> x::node<val_17_5230,next_17_5240> *  HP_535(next_17_5240,x),
HP_535(x0,x) * x::node<val_17_541,x0>&x0=null -> G(x,x0)}

constrs_ex1:{ HP_537(x0,x) * x::node<val_16_545,x0>&x0!=null -> H(x0)&true,
 x::node<val_16_545,x0> * H1(x0)&x0!=null-> H1(x)&true,
 H(x)&true-> x::node<val_16_525,next_16_526> * HP_537(next_16_526,x)&true,
 HP_537(x0,x) * x::node<val_16_543,x0>&x0=null-> H1(x)&true}


hp_defs:{true -> true,
true -> false}



