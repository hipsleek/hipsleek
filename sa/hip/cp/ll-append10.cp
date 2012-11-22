HeapPred HP_1(node a).
HeapPred HP_599(node a).
HeapPred HP_2(node a, node b).

append:SUCCESS[
ass [][]:{
   H1a(y) --> H1b(y);
   x::node<_,p> * G2(p,y) * H1b(y)&p!=null --> G2(x,y) * H1b(y);
   v_node_54_616=null --> H1b(y);
   H1a(y) * HP_599(p) * x::node<_,y>&p=null --> G2(x,y) * H1b(y);
   H1a(y) --> H1a(y);
   HP_599(p)& p!=null --> H1(p);
   H1(x) --> x::node<_,p> * HP_599(p)
 }

hpdefs [H1,H2,H1a,H1b,G1,G2][H1b_y_659]:{ 
 G2(x,y) --> x::node<_,p> * HP_2(p,y) & y = H1b_y_659;
 H1(x) -->  x::node<_,p>*HP_1(p);
 HP_2(x,p) --> x=p or x::node<_,p1> * HP_2(p1,p);
 HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
 H1a(y) -->  H1b(y);
 H1a(y) --> emp&y=H1b_y_659;
 H1b(y) --> emp&y=H1b_y_659
 }
]
