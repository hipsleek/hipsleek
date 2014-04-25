/* bubble sort */

data node {
	int val;
	node next;
}

sll<n,sm, lg> ==
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


ull<n, c,sm> ==
		self::node<sm, null> & n=1  & c=0
  or	self::node<sm, q> * q::ull<n-1, c1, qs> 
              & (sm<=qs & c=c1 | sm>qs & c=1+c1)
  /* or	self::node<sm, q> * q::ull<n-1,c, qs> & sm>qs */
	inv self!=null & n>=1 & 0<=c<n ;


//lemma self::sll<n, sm, lg> <- self::ll<n>;

//lemma self::sll<n, sm, lg> -> self::ll<n>;

lemma self::sll<n, sm, lg> -> self::ull<n,0,sm>;

/*
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
*/


bool bubble(node xs)
/*
	requires xs::ll<n> & n>0
	ensures xs::sll<n, s, l> & !res
		or  xs::ll<n> & res;
*/
  requires xs::ull<n,c,_> & n>0
  ensures xs::sll<n, s, l> & !res
  or  xs::ull<n,c1,_> & res & c1<=c;
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
		if (xv <= xnv) 
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
  requires xs::ull<n,c,_> & n>0
	ensures xs::sll<n, _, _>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}

void skip()


/*
  void bubble2 (node x)

{
  if (x==null|| x.next==null) return;
  else
    {

      if (x.val >= x.next.val) 
        { 
            swap (x); 
            bubble2(x.next); 
            if (x.val>=x.next.val) bubble2(x);
    }


}
*/
