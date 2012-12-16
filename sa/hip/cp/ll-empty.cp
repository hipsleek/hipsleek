
empty:SUCCESS[
ass [H1,G1][]:{
   H1(x)&x=null --> emp&true;
   emp&x=null --> G1(x)&true;
   H1(x)&x!=null --> G1(x)&true
}

hpdefs [H1,G1][]:{
   H1(x) --> HTrue&true;
   G1(x) --> H1(x)
 }
]
