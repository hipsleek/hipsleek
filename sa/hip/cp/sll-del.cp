HeapPred HP_1(node2 a).
HeapPred HP_555(node2 a).
HeapPred HP_548(node2 a).

delete:SUCCESS[
ass [H1,G1][]:{
  H1(x)&true --> x::node2<_,p>@M * HP_548(p);
  HP_548(v_node2_27_528') --> v_node2_27_528'::node2<_,p>@M * HP_555(p);
  HP_555(p) * v_node2_27_566::node2<_,p>@M& p!=null --> H1(v_node2_27_566);
  HP_555(v_node2_27_574)&v_node2_27_574=null --> emp&true;
  x::node2<val_27_554,next_29_534'>@M&next_29_534'=null --> G1(x)&true;
  x::node2<val_27_554,v_node2_27_566>@M * G1(v_node2_27_566)&true --> G1(x)
}

hpdefs [H1,G1][]:{
   H1(x) --> x::node2<val_27_526',next_27_527'>@M * 
        next_27_527'::node2<val_27_529',next_27_593>@M * HP_1(next_27_593);
   HP_1(x) --> x=null or x::node2<_,p1> * HP_1(p1);
   G1(x) --> x::node2<val_27_554,next_29_534'>@M * HP_1(next_29_534')
 }
]
