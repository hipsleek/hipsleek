HeapPred HP_558(node2 b).
HeapPred HP_559(node2 a).

count:SUCCESS[
ass [H1,G1][]:{
 H1(z)&z!=null --> z::node2<val_32_528',left_32_529',right_32_530'>@M * HP_558(left_32_529') * HP_559(right_32_530');
 HP_558(cleft_27')&true --> H1(cleft_27');
 HP_559(cleft_27')&true --> H1(cleft_27');
 H1(z)&z=null --> emp&true;
 emp&z=null --> G1(z)&true;
 HP_559(right_32_573) * z::node2<val_32_572,cleft_589,right_32_573> * G1(cleft_589)&true --> G1(z);
 HP_558(left_35_577) * z::node2<val_35_576,left_35_577,cleft_593> * G1(cleft_593)&true --> G1(z)
 }

hpdefs [H1,G1][]:{
  H1(z_609) --> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r);
  G1(z_608) --> z_608 = null or z_608::node2<_, l, r> * G1(l) * G1(r)

 }
]
