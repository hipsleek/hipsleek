/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg> == self::node<sm, null> & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n-1, qs, lg> & q!=null & sm<=qs & n > 1 & qs <= lg;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1> & n>0;


lemma self::sll<n, sm, lg> -> self::ll<n>;

void bsort(node xs)
	requires xs::ll<n> & n>0
	ensures xs::sll<n, _, _>;
{
	bool b;
  int aux, tmp1;
	bool tmp, flag; 

	if (xs.next == null) {
      b = false;
	}	else {
       bsort(xs.next);
       int xv = xs.val;
       int xnv = xs.next.val;
       if (xv <= xnv) 
            flag = false;
       else {
            xs.val = xnv;
            xs.next.val = xv;
            flag = true; 
        }
        b = flag;	
	}
	if (b) {
		bsort(xs);
	}
}
