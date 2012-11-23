/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg> ==
		self::node<sm, null> & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n-1, qs, lg> & q!=null & sm<=qs 
	inv n>=1 & sm<=lg;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

lemma self::sll<n, sm, lg> -> self::ll<n>;


ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));

lemma self::sll1<S> -> self::ll1<S>;


bool bubble(node xs)
	requires xs::ll<n> & n>0
	ensures xs::sll<n, s, l> & !res
    or  xs::ll<n> & res;

	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S> & !res
    or  xs::ll1<S> & res ;

{
	int aux, tmp1;
	bool tmp, flag; 

	if (xs.next == null) {
		return false;
	}
	else {    
		tmp = bubble(xs.next);
		int xv = xs.val;
		if (xs.val <= xs.next.val) 
			flag = false;
		else {
			xs.val = xs.next.val;
			xs.next.val = xv; 
			flag = true; 
		}
		return (flag || tmp);	
	}
}



void bsort(node xs)
	requires xs::ll<n> & n>0
	ensures xs::sll<n, _, _>;
/*	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S>;
*/

{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}


