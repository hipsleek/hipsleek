HeapPred HP_1(node a).
HeapPred HP_1a(node b).
HeapPred HP_1b(node b).

front:SUCCESS[
ass [F,G][]:{
    HP_1a(p) * x::node<v_int,p> --> G(x,v_int);
    F(x) --> x::node<_,p> *HP_1a(p)

	}

hpdefs [F,G][]:{
 F(x)    --> x::node<HP_1_n,n>;
 G(x,res) --> x::node<res,n> & res = HP_1_n

 }
]
//currently, we do not capture non_ptrs, so res = HP_1_n is not captured
/*
hpdefs [F,G]:{
 HP_1(p) --> htrue&true;
 F(x)    --> x::node<_,n> * HP_1(n);
 G(x,res) --> x::node<res,n> * HP_1(n)
*/
