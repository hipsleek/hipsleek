    
data node {
    node prev; 
    node next; 
    }

HeapPred H1(node a,node@NI b).
PostPred G1(node a,node@NI b).

dll<prev> == 
  self=null or 
  self::node<prev,n>* n::dll<self>;

bool check_dll (node l, node prv)
//requires l::dll<prv>@L ensures  res;
 infer [H1,G1] requires H1(l,prv) ensures G1(l,prv) & res;
{
	if (l==null) return true;
	else return (l.prev==prv) && check_dll(l.next,l);
}

/*
# check-dll.ss


[ H1(l,prv@NI)&l!=null --> l::node<prev_19_928,next_19_929>@M * 
  HP_930(prev_19_928,prv@NI) * HP_931(next_19_929,prv@NI),

 HP_931(next_19_929,prv@NI) --> H1(next_19_929,l@NI). // l??

 H1(l,prv@NI)&l=null --> G1(l,prv@NI),

 HP_930(prev_19_928,prv@NI) * l::node<prev_19_928,next_19_929>@M * 
  G1(next_19_929,l@NI)&prev_19_928=prv --> G1(l,prv@NI),

 HP_930(prev_19_928,prv@NI) --> emp&forall(l:(prev_19_928=prv | l=null))]



Below is similar to check-dll.ss, minus one
redundant assumption

[ H1(l,prv@NI)&l!=null --> l::node<prev_19_928,next_19_929>@M * 
  HP_930(prev_19_928,prv@NI) * HP_931(next_19_929,prv@NI),
 HP_931(next_19_929,prv@NI) --> H1(next_19_929,l@NI),
 H1(l,prv@NI)&l=null --> G1(l,prv@NI),
 HP_930(prev_19_928,prv@NI) * l::node<prev_19_928,next_19_929>@M * 
  G1(next_19_929,l@NI)&prev_19_928=prv --> G1(l,prv@NI),
 HP_930(prev_19_928,prv@NI) --> emp&forall(l:((prv>=prev_19_928 | l=null)) & 
  ((prev_19_928>=prv | l=null)))]

check-dll.ss yields:

[ H1(l,prv@NI)&l!=null --> l::node<prev_19_928,next_19_929>@M * 
  HP_930(prev_19_928,prv@NI) * HP_931(next_19_929,prv@NI),
 HP_931(next_19_929,prv@NI)&prev_19_928=prv --> H1(next_19_929,l@NI),
 ^^^^^^ extra assumption ^^^^
 HP_931(next_19_929,prv@NI) --> H1(next_19_929,l@NI),
 H1(l,prv@NI)&l=null --> G1(l,prv@NI),
 HP_930(prev_19_928,prv@NI) * l::node<prev_19_928,next_19_929>@M * 
  G1(next_19_929,l@NI)&prev_19_928=prv --> G1(l,prv@NI),
 HP_930(prev_19_928,prv@NI) --> emp&forall(l:((prv>=prev_19_928 | l=null)) & 
  ((prev_19_928>=prv | l=null)))]



*/
