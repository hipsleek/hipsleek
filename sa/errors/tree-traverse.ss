data node2 {
	int val;
	node2 left;
	node2 right; 
}

HeapPred H(node2 a).
HeapPred H1(node2 a).
HeapPred G(node2 a, node2 b).


void foo(ref node2 x)
	infer[H,G]
	requires H(x)
	ensures G(x,x');
{
	if (x != null)
	{
		if(x.left != null) foo(x.left);
		else foo(x.right);	
	}
}



/*
INPUT:
HP_550(v_node2_19_572,right_19_563,x) *  x::node2<val_19_562,v_node2_19_572,right_19_563>&v_node2_19_572!=null & x!=null --> H(v_node2_19_572)
x::node2<val_19_562,v_node2_19_572,right_19_563> * HP_592(right_19_563,v_node2_19_572,v_node2_19_591,x,x)&v_node2_19_572!=null & x!=null--> G(x,x)
H(x)&x!=null--> x::node2<val_19_522',left_19_523',right_19_524'> * HP_550(left_19_523',right_19_524',x)
HP_550(v_node2_19_583,right_19_559,x) * x::node2<val_19_558,v_node2_19_583,right_19_559>&v_node2_19_583=null & x!=null --> H(right_19_559)
x::node2<val_19_558,v_node2_19_583,right_19_559>&x!=null --> G(x,x)
H(x)&x=null--> G(x,x)

PARTIAL DEF:

HP_550(v_node2_19_583,right_19_559) --> v_node2_19_583=null --> emp (*WRONG*)
H(x) --> x=null--> emp

G(x,x) <--> G_595(x) * G_596(x)

x::node2<val_19_562,v_node2_19_572,right_19_563>&v_node2_19_572!=null & x!=null --> G_595(x)
x::node2<val_19_562,v_node2_19_572,right_19_563>&v_node2_19_572!=null & x!=null--> G_596(x)	(*NOT ENOUGH*)
x::node2<val_19_558,v_node2_19_583,right_19_559>&x!=null --> G_595(x)
x::node2<val_19_558,v_node2_19_583,right_19_559>&x!=null --> G_596(x)
x=null--> G_595(x)
x=null--> G_596(x)

norm by hand 
1.H1(v,r,x) *  x::node2<v1,v,r> & v1!=null & x!=null --> H(v1)
2.x::node2<v1,v,r> * H2(r,v,v2,x,x)&v!=null & x!=null--> G1(x)
3.H(x) & x!=null--> x::node2<v',l',r'> * H1(l',r',x)
4.H1(v4,r,x) * x::node2<v5,v4,r> & v4 = null & x!=null --> H(r)
5.x::node2<v,v4,r>&x!=null --> G1(x)
6.H(x)&x=null--> G1(x)

(2) check eq, subst (optional)

(3) pick partial defs:
6. x=null -> H(x)
x=null-> G1(x)
4 + 3
H1(v4,r,x) * x::node2<v5,v4,r> & v4 = null & x!=null & r!=null--> x::node2<v',l',r'> * H1(l',r',x)


*/

/*
void foo(ref node2 x)
	infer[H,G]
	requires H(x)
	ensures G(x,x');
{
	if (x != null)
	{
		if(x.left != null) foo(x.left);
		else foo(x.right);	
	}
}
INFER BY HAND

H(x)
//if
H(x) & x != null
H(x) & x = null
=============
then branch:
H(x) & x != null
x.left: H(x) & x != null -> x::node<l,r> * H1(x,l,r)
	H1(x,l,r) * x::node<l,r> & x != null
constr: H(x) & x != null -> x::node<l,r> * H1(x,l,r)

//condition: x.left != null
then-branch
H1(x,l,r) * x::node<l,r> & x != null & l != null
H1(x,l,r) * x::node<l,r> & x != null & l != null -> H(l) -> G(l,l')
	G(l,l') * H1(x,l,r) * x::node<l,r> & x != null & l != null 
constr: H1(x,l,r) * x::node<l,r> & x != null & l != null -> H(l)

G(l,l') * H1(x,l,r) * x::node<l,r> & x != null & l != null -> G(x,x')
else-branch
H1(x,l,r) * x::node<l,r> & x != null & l = null
H1(x,l,r) * x::node<l,r> & x != null & l = null -> H(r) -> G(r,r')
	G(r,r') * H1(x,l,r) * x::node<l,r> & x != null & l = null 
constr: H1(x,l,r) * x::node<l,r> & x != null & l = null -> H(r)
	G(r,r') * H1(x,l,r) * x::node<l,r> & x != null & l = null -> G(x,x')

else-branch
H(x) & x = null -> G(x,x')

constrs:
H(x) & x != null -> x::node<l,r> * H1(x,l,r)
H1(x,l,r) * x::node<l,r> & x != null & l != null -> H(l)
G(r,r') * H1(x,l,r) * x::node<l,r> & x != null & l = null 
G(r,r') * H1(x,l,r) * x::node<l,r> & x != null & l = null -> G(x,x')
H(x) & x = null -> G(x,x')

NORMALIZATION
=================================
input:
1. H(x) & x != null -> x::node<l,r> * H1(x,l,r)
2. H1(x,l,r) * x::node<l,r> & x != null & l != null -> H(l)
3. G(l,l') * H1(x,l,r) * x::node<l,r> & x != null & l != null -> G(x,x')
4. G(r,r') * H1(x,l,r) * x::node<l,r> & x != null & l = null -> G(x,x')
5. H(x) & x = null -> G(x,x')
elem: no
(consider:
drop h1,1
1. H(x) & x != null -> x::node<l,r> * H1(l,r)
2. H1(l,r) * x::node<l,r> & x != null & l != null -> H(l)
3. G(l,l') * H1(l,r) * x::node<l,r> & x != null & l != null -> G(x,x')
4. G(r,r') * H1(l,r) * x::node<l,r> & x != null & l = null -> G(x,x')
5. H(x) & x = null -> G(x,x')
split
1. H(x) & x != null -> x::node<l,r> * H11(l) * H12(r)
2. H11(l) * H12(r) * x::node<l,r> & x != null & l != null -> H(l)
3. G1(l) * G1(l') *H11(l) * H12(r) * x::node<l,r> & x != null & l != null -> G1(x)
4. G(r,r') * H11(l) * H12(r) * x::node<l,r> & x != null & l = null -> G(x,x)
5. H(x) & x = null -> G(x,x)








*/

