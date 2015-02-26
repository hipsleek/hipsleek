// Example from Radu Iosif
data node {
	node left;
	node right;
	node parrent;
	node successor;
}

 tll<p,ll,lr> = self::node<null,null,p,lr> & self = ll
	or self::node<l,r,p,null> * l::tll<self,ll,z> * r::tll<self,z,lr>;

 tree<p> = self::node<null,null,p,_>
	or self::node<l,r,p,null> * l::tree<self> * r::tree<self>;

 tree_left<p,ll> = self::node<null,null,p,_> & self = ll
	or self::node<l,r,p,null> * l::tree_left<self,ll> * r::tree_left<self,_>;

lemma self tree<p><-> exists l.self::tree_left<p,l>.

//linked_leaves_str y,z,q;

node get_left (node x)
	requires x::tree<p> ensures x::tree_left<p,ll>& res=ll;
{
	if (x.left=null) return x;
	else get_left(x.left);
}

void tll2(node x, node y, node z, node q) 
requires x::tree<> ensures x::tll<_,_>;
{
	q = get_left(x);
	x = q;
	y = q.parrent;
	while (!y==NULL) {
		z=y.right;
		if (z==y) {
			q=y;
		} else {
			q = y/right;
			y = q.left;
			q = get_left(y);
			x.successor=q;
			x=q;
		}		
		y=q->parrent;
	}
}


/*
typedef struct linked_leaves_str {
	struct linked_leaves_str *left;
	struct linked_leaves_str *right;
	struct linked_leaves_str *parrent;
	struct linked_leaves_str *successor;
}* linked_leaves_str;

linked_leaves_str y,z,q;

/* We suppose, that the data structure is on the beginning pointed by variable x */

void main2(linked_leaves_str x) {
	y=x->left;	
	while (! y==NULL) {
		x=y;
		y=x->left;	
	}
	q=x;
	y=q->parrent;
	while (!y==NULL) {
		z=y->right;
		if (z==y) {
			q=y;
		} else {
			q=y->right;
			y=q->left;
			while (! y==NULL) {
				q=y;
				y=q->left;
			}
			x->successor=q;
			x=q;
		}		
		y=q->parrent;
	}
}


*/
