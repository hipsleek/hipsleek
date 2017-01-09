/* bubble sort */

data node {
  int val;
  node next;
}

sll<n, sm> ==
  self::node<sm, null> &  n=1 or 
  self::node<sm, q> * q::sll<n-1, qs> & q!=null & sm<=qs 
  inv n>=1 ;

ll<n> == self=null & n=0
  or self::node<_, r> * r::ll<n-1>
  inv n>=0;

/*
lls<n,k,mx> == 
  self::node<mx, null> & n=1 & k=1 or 
  self::node<v, r> * r::lls<n-1,k-1,mx> & k>1 & v<=mx or
  self::node<v, r> * r::lls<n-1,k,mx> & k=1 & mx<=v
  inv n>=k & k>=1;
*/

lls<n,k,mx> == case {
  k=0 -> [] self=null & n=0 or
            self::node<v, r> * r::lls<n-1, k, mx> & mx<=v;
  k=1 -> [] self::node<mx, r> * r::lls<n-1, k-1, mx>;
  (k!=0) & (k!=1) -> [] self::node<v, r> * r::lls<n-1, k-1, mx> & v<=mx;  
} inv n>=k & k>=0;

lemma self::sll<n, sm> -> self::lls<n,n,sm>;

bool bubble(node xs)
/*
  requires xs::ll<n> & n>0
  ensures xs::sll<n, s, l> & !res
    or  xs::ll<n> & res;
*/
  requires xs::lls<n, k, mx> & n>0
  ensures xs::lls<n, k+1, mx1> & mx<=mx1 & res or
          xs::sll<n, mx> & !res;
{
  int aux, tmp1;
  bool tmp, flag; 

  if (xs.next == null) {
          assume false;
          return false;
  }
  else {
          assume false;
          tmp = bubble(xs.next);
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
          return (flag || tmp);	
  }
}


void bsort(node xs)
  requires xs::lls<n,k,mx> & n>0
  ensures xs::sll<n,mx1> & mx<=mx1;
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

