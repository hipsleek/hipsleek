/* bubble sort */

data node {
	int val;
	node next;
}



sll<"n":n, "sm":sm, "sm":lg, "S":S> ==
		self::node<sm, null> & ["n": n=1; "sm": sm =lg; "S": S = {sm}]
	or	self::node<sm, q> * q::sll<n1, qs, lg, S1> & q!=null & ["n": n1 = n-1; "sm": sm <= qs; "S": S = union(S1,{sm})] 
	inv true & ["n": n>=1; "sm": sm<=lg];

bnd<"n":n, "sn":sn, "bg":bg, "Sb":Sb> == 
	    self=null  & ["n": n=0; "Sb": Sb = {}]
	or  self::node<d,p> * p::bnd<n2,sn,bg,Sb1> & ["n": n2 = n-1; "sn": sn <= d < bg; "Sb": Sb = union(Sb1,{d})]
	inv true & ["n": n>=0];

ll<n, S> == self=null & n=0 & S={}
	or self::node<_, r> * r::ll<n-1,_>
	inv n>=0;
	
	

//lemma self::sll<n, sm, lg, S> -> self::bnd<n,_,_, _>;
lemma self::sll<n, sm, lg, S> -> self::ll<n,_>;

//------------------------------------------------------------

// ------------------ FUNTIONS -----------------------------//

bool bubble(node xs)
	requires xs::bnd<n, sn, bg, Sb> & n>0 or xs:: ll <n,_> & n >0
	ensures xs::sll<n, sm, lg, S> & !res & Sb = S
	or xs::sll<n,_, _, S1> & n>=0 & res ;
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
			xs.val = xs.next.val; 
			//xs.next.val = aux;
			flag = true; 
		}
		
		return (flag || tmp);	
	}
}

void bsort(node xs)
	requires xs::bnd<n, _,_,Sb> & n>10 & ["Sb": Sb!={}] or xs::ll<n,_> & n >0
	ensures xs::sll<n, _, _,Sb>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}



	
