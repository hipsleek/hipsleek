constrs []:{ HP_535(x0,x) &x0!=null -> H(x0),
x::node<val_17_543,x_552> * G(x_552,x0)&x_552!=null -> G(x,x0),
H(x) -> x::node<val_17_5230,next_17_5240> *  HP_535(next_17_5240,x),
HP_535(x0,x) * x::node<val_17_541,x0>&x0=null -> G(x,x0)}



hp_defs [H]:{ll(b) -> b = null or b::node<_,c> * ll(c),
 H(x) -> x::node<_,b> * H1(b),
H1(b) -> b = null or b::node<_,c> * H1(c)
}


constrs_ex1 []:{ HP_537(x0,x) * x::node<val_16_545,x0>&x0!=null -> H(x0)&true,
 x::node<val_16_545,x0> * H1(x0)&x0!=null-> H1(x)&true,
 H(x)&true-> x::node<val_16_525,next_16_526> * HP_537(next_16_526,x)&true,
 HP_537(x0,x) * x::node<val_16_543,x0>&x0=null-> H1(x)&true}


/*

G(x,x')::  
 x::node<val_18_547,x_556> * G(x_556,x')&x_556!=null
 or x::node<val_18_545,x'>&x'=null
 ,
HP_539(x')::  
 emp&x'=null
 or x'::node<val_18_527',next_18_528'> * HP_539(next_18_528')&true
 ,
H(x)::  x::node<val_18_527',next_18_528'> * HP_539(next_18_528')&true]


HP_RELDEFN HP_560:  HP_560(x)::  
 x::node<val_18_547,x_556> * HP_560(x_556)&x_556!=null
 or x::node<val_18_545,x'>&x'=null
 ,
HP_RELDEFN HP_539:  HP_539(x')::  
 emp&x'=null
 or x'::node<val_18_527',next_18_528'> * HP_539(next_18_528')&true
 ,
HP_RELDEFN HP_561:  HP_561(x')::  emp&x'=null,
HP_RELDEFN H:  H(x)::  x::node<val_18_527',next_18_528'> * HP_539(next_18_528')&true,
HP_RELDEFN G:  G(x,x')::  HP_560(x) * HP_561(x')&true

*/
