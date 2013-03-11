/* bubble sort */

data node {
	int val;
	node next;
}


ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));

lemma self::sll1<S> -> self::ll1<S>;

bool bubble(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S> & !res
		or  xs::ll1<S> & res ;
{
	int aux;
	bool tmp, flag; 

	if (xs.next == null) {
		return false;
	}
	else {
		flag = false;
		tmp = bubble(xs.next);
		if (xs.val > xs.next.val) {
			aux = xs.val;
			xs.val = xs.next.val;
			xs.next.val = aux; 
			flag = true; 

			/*if (!tmp) {
				if (xs.next.next != null) { // this is the lemma step
					id1(xs.next.next);
				}
			}*/
		}
		return (flag || tmp);	
	}
}


void bsort(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}



bool bubble(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S> & !res or  xs::ll1<S> & res ;
{
	if (xs.next == null) { return false; } 
    else {
		bool tmp = bubble(xs.next);
		if (xs.val > xs.next.val) {
			int aux = xs.val;
			xs.val = xs.next.val;
			xs.next.val = aux; 
			return true; 
		}
		return tmp;	
	}
}

void bsort(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S>;
{ if (bubble(xs)) { bsort(xs); } }
