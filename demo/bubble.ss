/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg> ==
		self::node<sm, null> & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n-1, qs, lg> & q!=null & sm<=qs 
	inv n>=1 & sm<=lg;

bnd<n,sm:int,bg> ==
 		self=null & n=0
  or	self::node<d,p> * p::bnd<n-1,sm,bg> & sm <= d< bg 
	inv n >= 0;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

lemma self::sll<n, sm, lg> <- self::ll<n>;

lemma self::sll<n, sm, lg> -> self::ll<n>;


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
	requires x::sll<n, sm, lg> //& n=1
	ensures x::ll<n>;
{
  node y = x.next;  
	if (y != null) {    
   // dprint;
   // assert y'::sll<_,_,_>; 
	//	assume false;
    id3(y);
	}  
  //assume false;  
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
    int xv = xs.val;
    int xnv = xs.next.val;
		if (xv >= xnv) 
			flag = false;
		else {
			xs.val = xnv;
			xs.next.val = xv; //ERROR: lhs and rhs do not match
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

void skip()
