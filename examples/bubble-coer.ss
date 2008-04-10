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

coercion self::sll<n, sm, lg> -> self::ll<n>;
/*
{
	if (x.next != null) {
		id3(x.next);
	}
}
*/

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
		if (xs.val > xs.next.val) {
			flag = false;
		}
		else {
			//aux = xs.val;
			//xs.val = xs.next.val;
			//xs.next.val = aux;
			flag = true;
		}
		return (flag || tmp);	
	}
}

void bsort(node xs)
	requires xs::ll<n> & n>0
	ensures xs::sll<n, _, _>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}


/*
void skip()
*/
