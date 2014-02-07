    
data node {
    node prev; 
    node next; 
    }

HeapPred H1(node a,node@NI b,node@NI c).
  PostPred G1(node a,node@NI b,node@NI c).

  cdll<prev,p> == 
  self=p or 
  self::node<prev,n>* n::cdll<self,p>;

bool check_cdll (node l, node prv, node p)
//  requires l::cdll<prv,p>@L ensures  res;
  infer [H1,G1] requires H1(l,prv,p) ensures G1(l,prv,p) & res;
{
	if (l==p) return true;
	else { bool r1 = check_cdll(l.next,l,p);
               bool e1 = (l.prev==prv);
               return e1 && r1;
             }
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
