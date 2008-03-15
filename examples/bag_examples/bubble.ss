/* bubble sort */

data node {
	int val;
	node next;
}

//------------------------------------------------------------------------------------------
// views
//------------------------------------------------------------------------------------------

sll<n, sm, lg> == self::node<sm, null> & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n1, qs, lg> & q!=null & sm<=qs & n = n1+1
	inv n>=1 & sm<=lg;

bnd<n,sm,bg> == self=null & n=0
   	or self::node<d,p> * p::bnd<n1,sm,bg> & sm <= d < bg & n = n1+1
	inv n >= 0;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n1> & n = n1+1
	inv n>=0;

/*ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));*/


void id3(node x)
	requires x::sll<n, sm, lg>
	ensures x::ll<n>;
{
	if (x.next != null) {
		id3(x.next);
	}
}

/*void id1(node x)
	requires x::sll1<S>
	ensures x::ll1<S>;
{
	if (x.next != null) {
		id1(x.next);
	}
}
*/
//------------------------------------------------------------------------------------------
// bubble functions
//------------------------------------------------------------------------------------------


bool bubble(node xs)
	requires xs::ll<n> & n>0
	ensures xs::sll<n, s, l> & !res
		or  xs::ll<n> & res;
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
			xs.next.val = aux; //swap(xs);
			flag = true; 

			if (!tmp) {
				if (xs.next.next != null) { // this is the coercion step
					id3(xs.next.next);
				}
			}
		}
		return (flag || tmp);	
	}
}

/*bool bubble1(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S> & !res
		or  xs::ll1<S> & res;
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
}*/


//------------------------------------------------------------------------------------------
// bsort functions
//------------------------------------------------------------------------------------------

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
void bsort1(node xs)
	requires xs::ll1<S> & S != {}
	ensures xs::sll1<S>;
{
	bool b;

	b = bubble1(xs);
	if (b) {
		bsort1(xs);
	}
}*/

