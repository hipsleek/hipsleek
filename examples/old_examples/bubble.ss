/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg> ==
		self::node<sm, null> & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n-1, qs, lg> & q!=null & sm<=qs 
	inv n>=1 & sm<=lg;

bnd<n,sm,bg> ==
 		self=null & n=0
   	or	self::node<d,p> * p::bnd<n-1,sm,bg> & sm <= d < bg 
	inv n >= 0;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

coercion id(node xs)
	requires xs::sll<n, sm, lg>
	ensures xs::ll<n>;
/*{
	if (xs.next == null)
	{
		return xs;
	}
	else
	{
		node tmp = xs.next;
		xs.next = id(tmp);
		return xs;
	}
}*/


node id2(node xs)
	requires xs::sll<n, sm, lg>
	ensures res::ll<n>;
{

	if (xs.next != null) {
		node tmp = xs.next;
		xs.next = id2(tmp);
	}
	return xs;
}

void id3(node x)
	requires x::sll<n, sm, lg>
	ensures x::ll<n>;
{
	if (x.next != null) {
		id3(x.next);
	}
}

bool bubble(node xs)
	requires xs::ll<n> & n>0
	ensures xs::sll<n, s, l> & !res
		or  xs::ll<n> & res;
{
	int aux, tmp1;
	bool tmp, flag; 

	if (xs.next == null) {
		return false;
	}
	else {
		tmp = bubble(xs.next);
		if (xs.val <= xs.next.val) {
			flag = false;
		}
		else {
			aux = xs.val;
			tmp1 = xs.next.val;
			xs.val = tmp1;
			xs.val = xs.next.val; //ERROR: lhs and rhs do not match
			//xs.next.val = aux;
			flag = true; 
/*
			if (!tmp) {
				if (xs.next.next != null) { // this is the coercion step
					//node tmp2 = xs.next.next;
					//xs.next.next = id(tmp2);
					id3(xs.next.next);
				}
			}
*/
		}
		return (flag || tmp);	
	}
}

void bsort(node xs)
	requires xs::ll<n> & n>10
	ensures xs::sll<n, _, _>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}

void skip()
