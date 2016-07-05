data node {
	int val;	
	node left;
	node right;
	node parent;
}

treep<p> == self=null
	or self::node<_,l,r,p> * l::treep<self> * r::treep<self>;

uptree<c> == self=null
	or self::node<_,l,r,p> * l::treep<self> * p::uptree<self> & r=c
	or self::node<_,l,r,p> * r::treep<self> * p::uptree<self> & l=c;

tptr<> == self=null
	or self::node<_,l,r,p> * l::treep<self> * r::treep<self> * p::uptree<self>;

/*
void t1(node x)
	requires x::tptr<>
	ensures true;
{
	if (x != null) {
		if (choice()) {
			t1(x.left);
		}
		else if (choice()) {
			t1(x.right);
		}
		else {
			t1(x.parent);
		}
	}
}
*/

bool choice() requires true ensures true;

/*
treep2<p> == self=null
	or self::node<_,l,r,p> * l::treep<self> * r::treep<self> * p::pv<
*/

/*
void insert(node x, int v) 
	requires x::treep<p> & x!=null
	ensures x::treep<_>;
{
	node tmp = new node(v, x.left, null, x);
	x.left = tmp; 
}

node test()
	requires true
	ensures res::treep<_>;
{
	node tmp1 = new node(1, null, null, null);
	node tmp2 = new node(2, tmp1, null, null);
	tmp1.parent = tmp2;
	return tmp2;
}

void up_root(node x)
	requires x::treep<p> & x!=null
	ensures true;
{
	if (x.parent != null) {
		up_root(x.parent);
	}
}
*/
