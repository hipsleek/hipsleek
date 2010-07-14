/* bubble sort */

data node {
	int val;
	node next;
}

//------------------------------------------------------------------------------------------
// views
//------------------------------------------------------------------------------------------


ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));

//insert to last
void id1(node x)
	requires x::sll1<S> & S != {}
	ensures x::ll1<S>;
  {
 	if (x.next != null) {
 		id1(x.next);
 	}
 }

//------------------------------------------------------------------------------------------
// bubble function
//------------------------------------------------------------------------------------------
bool bubble1(node xs)
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
		tmp = bubble1(xs.next);
		if (xs.val > xs.next.val) {
			aux = xs.val;
			xs.val = xs.next.val;
			xs.next.val = aux; //swap(xs);
			flag = true; 

			if (!tmp) {
				if (xs.next.next != null) { // this is the coercion step
					id1(xs.next.next);
				}
			}
		}
		return (flag || tmp);	
	}
}


//------------------------------------------------------------------------------------------
// bsort function
//------------------------------------------------------------------------------------------

void bsort1(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S>;
{
	bool b;

	b = bubble1(xs);
	if (b) {
		bsort1(xs);
	}
}

