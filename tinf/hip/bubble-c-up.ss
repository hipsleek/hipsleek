/* bubble sort */

data node {
  int val;
  node next;
}

sll<n, sm> ==
  self=null & n=0 & sm=\inf or	
  self::node<sm, q> * q::sll<n-1, qm> & q!=null & sm <= qm 
  inv n>=0;

uls<n, lg, tl> ==
  self=tl & n=0 & lg=-\inf or
  self::node<v, q> * q::uls<n-1, lg1, tl> & lg = max(v, lg1) & q!=null
  inv n>=0;

bool bubble(node xs)
	//requires xs::sll<n, sm>@L & n > 0
	//ensures !res; //unchanged

	//requires xs::node<v, p> * p::sll<n, sm> & v <= sm
	//ensures !res;

	/*
	requires xs::uls<n1, lg, p> * p::sll<n2, sm> & n2 > 0 & lg <= sm
	case {
		n1 = 0 -> ensures xs::sll<n2, sm> & !res;
		n1 != 0 -> 
			//ensures xs::uls<n1-n, lg1, q> * q::sll<n2+n, lg> & lg1 <= lg & 0 < n & n <= n1;
			ensures xs::uls<n1-1, lg1, q> * q::sll<n2+1, lg> & lg1 <= lg;
	}
	*/

	// unchanged if xs is sorted; otherwise, changed
	requires xs::uls<n1, lg, p> * p::sll<n2, sm> & lg <= sm & Term[n1, n2]
	case {
		n1 = 0 -> requires n2 > 0 ensures xs::sll<n2, sm> & !res;
		n1 != 0 -> ensures xs::uls<n1-1, lg1, q> * q::sll<n2+1, lg> & lg1 <= lg;
	}
{
	bool tmp, flag; 

	if (xs.next == null) {
    return false;
	}
	else {
    //tmp = bubble(xs.next);
    int xv = xs.val;
    int xnv = xs.next.val;
    if (xv <= xnv) 
      flag = false;
    else {
      xs.val = xnv;
      xs.next.val = xv; 
      flag = true; 
    }
		tmp = bubble(xs.next);
    return (flag || tmp);	
	}
}

void bsort(node xs)
	requires xs::uls<n1, lg, p> * p::sll<n2, sm> & n1 + n2 > 0 & lg <= sm & Term[n1]	
	ensures true;
{
  bool b;

  b = bubble(xs);
  if (b) {
    bsort(xs);
  }
}
