/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm> ==
		self::node<sm, null> &  n=1 
	or	self::node<sm, q> * q::sll<n-1, qs> & q!=null & sm<=qs 
	inv n>=1 ;

bnd<n,sm:int,bg> ==
 		self=null & n=0
  or	self::node<d,p> * p::bnd<n-1,sm,bg> & sm <= d< bg 
	inv n >= 0;

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;

//lemma self::sll<n, sm, lg> <- self::ll<n>;


/*
lls<n,k,sm> == self=null & n=0 & k=0 & sm=\inf
  or self::node<v, r> * r::lls<n-1,k,sm> & n>k & v<=sm
  or self::node<sm, r> * r::lls<n-1,k-1,sm1> & n=k & sm<=sm1
	inv n>=k & k>=0;
*/

lls<n,k,sm> == case {
    n=k -> [] self=null & n=0  & sm=\inf 
         or self::node<sm,r>*r::lls<n-1,k-1,sm1> & sm<=sm1;
    n!=k -> [] self::node<v, r> * r::lls<n-1,k,sm> & n>k & v<=sm;
}	inv n>=k & k>=0;

lemma self::sll<n, sm> -> self::lls<n,n,sm>;


bool bubble(node xs)
/*
	requires xs::ll<n> & n>0
	ensures xs::sll<n, s, l> & !res
		or  xs::ll<n> & res;
*/
  requires xs::lls<n,k,sm> & n>0  & Term[n]
  case {
    k=n -> ensures xs::sll<n,sm> & !res;
    k!=n -> ensures xs::sll<n, s> & !res & s<=sm
              or  xs::lls<n,k1,sm1> & res & k1=k+1 & sm1<=sm;
  }
{
	int aux, tmp1;
	bool tmp, flag; 

	if (xs.next == null) {
          //assume false;
          return false;
	}
	else {
          //tmp = bubble(xs.next);
          int xv = xs.val;
          int xnv = xs.next.val;
          if (xv <= xnv) {
            //assume false;
            flag = false;
          }
          else {
            xs.val = xnv;
            xs.next.val = xv; //ERROR: lhs and rhs do not match
            flag = true; 
            //dprint;
            //assume false;
          }
					tmp = bubble(xs.next);
          return (flag || tmp);	
	}
}


void bsort(node xs)
  requires xs::lls<n,k,sm> & n>0 & Term[n-k]
  ensures xs::sll<n,sm1> & sm1<=sm;
     /*
	requires xs::ll<n> & n>0
	ensures xs::sll<n, _, _>;
     */
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}

void skip()


/*

!!! processing primitives "["prelude_inf.ss";"prelude.ss"]
Starting Omega...oc
warning fast_imply : not normalisedwarning fast_imply : not normalised

 bsort verifies but not bubble..
*/
