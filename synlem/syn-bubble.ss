/* bubble sort */

data node {
	int val;
	node next;
}

sll<n, sm, lg> ==
		self::node<sm, null> & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n-1, qs, lg> & q!=null & sm<=qs 
	inv n>=1 & sm<=lg;


ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1>
	inv n>=0;


//lemma self::sll<n, sm, lg> -> self::ll<n>;


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
    if (xv <= xnv)
      flag = false;
    else {
      xs.val = xnv;
      xs.next.val = xv; //ERROR: lhs and rhs do not match
      flag = true;
    }
    return (flag || tmp);
    //dprint;
    //SYN LEMMA HERE
    // xs::ll<n> & res;
  }
}

/*
 gen lemma: 
self::sll<flted_10_1112,qs_1114,lg_1111>@M&0<n 
 & 0<flted_15_1021 & n=flted_15_1021+1 
 & 0<=flted_15_1021 & Anon_1355<Anon_1022 
 & flted_15_1021=flted_10_1112+1 & self!=null 
 & Anon_1355<=qs_1114&
 {FLOW,(24,25)=__norm}[] 
 <-  self::ll<flted_15_1366>@M&{FLOW,(1,27)=__flow}[]

 gen lemma: 
 r_1121::ll<flted_15_1119>@M * self::node<_,r_1121>@M&0<n 
  & 0<flted_15_1021 & n=flted_15_1021+1 & 0<=flted_15_1021 
  & flted_15_1021=flted_15_1119+1 & Anon_1120<Anon_1022
  &{FLOW,(24,25)=__norm}[] 
  <-  self::sll<flted_10_1621,qs_1624,lg_1618>@M
  &{FLOW,(24,25)=__norm}[]


 */
