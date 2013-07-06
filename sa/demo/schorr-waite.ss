data node {
 int mark;
 int swing;
 node left;
 node right;
}

HeapPred H(node a).
HeapPred G(node a,int x).

tree<v> == self=null
 or self::node<0,_,p,q> * p::tree<0> * q::tree<0> & v = 0
 or self::node<0,_,p,q> * p::tree<_> * q::tree<_> & v = 1
 or self::node<1,_,p,q> * p::tree<2> * q::tree<2> & v = 2
 inv true;

void traverse(node t, node p)
requires t::tree<_> * p::tree<_>
ensures t::tree<_> * p::tree<_>;
/*
infer[H,G]
requires H(t) * H(p)
ensures G(t,2) * G(p,2);
*/
{ 
  node x,y;
  if (t == null) return;
  if (p != null || t.mark == 1){
  	if(t.mark == 1) { //push
  		x = p;
		p = t;
		t = t.left;
		p.left = x;
		p.swing = 0;
		p.mark = 1;
	}
	else {
		if (p.swing == 0) { //swing
			x = t;
			t = p.right;
			y = p.left;
			p.right = y;
			p.left = x;
			p.swing = 1;
		}
		else { //pop
			x = t;
			t = p;
			p = p.right;
			t.right = x;
		}
	}
	traverse(t,p);
  }
  else return;
}
