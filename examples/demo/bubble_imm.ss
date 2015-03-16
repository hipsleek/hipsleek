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


bool bubble(node xs, ref node r)
	requires xs::ll<n>@I & n>0
	ensures r'::sll<n, s, l> & !res
		or  r'::ll<n> & res;
{
	int aux, tmp1;
	bool tmp, flag;
	node tmp_node;

	if (xs.next == null) {
		r = new node(xs.val, null);	   
		return false;
		}
	else {  
		tmp = bubble(xs.next, tmp_node);
		r = new node(xs.val, tmp_node);
		int xv = r.val;
		int xnv = r.next.val;
		if (xv <= xnv) 
			flag = false;
		else {
			r.val = xnv;
			r.next.val = xv; //ERROR: lhs and rhs do not match
			flag = true; 
		}
		return (flag || tmp);	
	}
}


node bsort(node xs)
	requires xs::ll<n>@I & n>0
	ensures res::sll<n, _, _>;
{
	bool b;
	node r;

	b = bubble(xs, r);
	if (b) {
		return bsort(r);
	}
	else return r;
}

void skip()
