/* LOC: 55 */
/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg> ==
		self::node<sm, null> & n=1 & sm = lg 
	or	self::node<sm, q> * q::sll<n1, qs, lg> & q!=null &  n1 = n-1 & sm <= qs 
	inv n>=1 & sm <= lg;

bnd<n, sn, bg> == 
	    self=null & n=0 & sn = bg
	or  self::node<d,p> * p::bnd<n2,sn,bg> & n2 = n-1 & sn <= d <= bg
	inv n>=0 & sn <= bg;

ll<n> == self=null & n=0 
	or self::node<d, r> * r::ll<n-1>
	inv n>=0;

//coercion self::sll<n, sm, lg, S> -> self::bnd<n,_,_, _>;
lemma self::sll<n, sm, lg> -> self::ll<n>;
lemma self::sll<n, sm, lg> -> self::bnd<n, sm, lg>;

//------------------------------------------------------------

// ------------------ FUNTIONS -----------------------------//

bool bubble(node xs)
	requires xs:: bnd<n, sm, lg> & n>0 & Term[n]
	ensures xs::sll<n, sm, lg> & !res
		   or xs::node<v, xn> * xn::bnd<n-1, sm1, lg> & sm<=v & v<=sm1 & !res;
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
			xs.next.val = aux;
			flag = true; 
		}
		
		return (flag || tmp);	
	}
}

void bsort(node xs)
	requires xs::bnd<n, sm, lg> & n>0 & Term 
	ensures xs::sll<n, sm, lg>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		if (xs.next != null) 
			bsort(xs.next);
	}
}



	
