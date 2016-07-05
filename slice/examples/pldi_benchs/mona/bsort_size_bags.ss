/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg, S> ==
		self::node<sm, null> & n=1 & sm =lg & S = {sm}
	or	self::node<sm, q> * q::sll<n1, qs, lg, S1> & q!=null &  n1 = n-1 & sm <= qs 
	& S = union(S1,{sm}) & forall (a: (a notin S | a >= sm))
	inv n>=1 & sm<=lg;

bnd<n, sn, bg, Sb> == 
	    self=null  &  n=0 & Sb = {}
	or  self::node<d,p> * p::bnd<n2,sn,bg,Sb1> & n2 = n-1 & sn <= d < bg & Sb = union(Sb1,{d})
	inv n>=0;

ll<n, S> == self=null & n=0 & S={}
	or self::node<d, r> * r::ll<n-1,S2> & S=union(S2,{d}) 
	inv n>=0;
	
//coercion self::sll<n, sm, lg, S> -> self::bnd<n,_,_, _>;
coercion self::sll<n, sm, lg, S> -> self::ll<n,S>;

//------------------------------------------------------------

// ------------------ FUNTIONS -----------------------------//

bool bubble(node xs)
	requires xs:: ll <n,S> & n >0
	ensures xs::sll<n, sm, lg, S> & !res
	or xs::ll<n, S> & res;
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
	requires xs::ll<n, S> & n>0 
	ensures xs::sll<n, _, _, S>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}



	
