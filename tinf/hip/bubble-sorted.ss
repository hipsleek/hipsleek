/* bubble sort */

data node {
  int val;
  node next;
}

sll<n, sm> ==
  self = null & n = 0 & sm = \inf or  
  self::node<sm, q> * q::sll<n-1, qm> & sm <= qm 
  inv n >= 0;

uls<n, lg, tl> ==
  self=tl & n=0 & lg=-\inf or
  self::node<v, q> * q::uls<n-1, lg1, tl> & lg = max(v, lg1)
  inv n>=0;

ls<n, sm, lg, srt, tl> ==
  self = tl & n = 0 & sm = \inf & lg = -\inf & srt = 1 or
  self::node<v, q> * q::ls<n-1, sm1, lg1, srt1, tl> & 
    sm = min(v, sm1) & lg = max(v, lg1) & (v > sm1 & srt = 0 | v <= sm1 & srt = srt1)
  inv 0 <= srt <= 1 & n >= 0;

bool bubble(node xs)
  // unchanged (!res) if xs is sorted; otherwise (res), changed
  /*
  requires xs::uls<n1, lg, p> * p::sll<n2, sm> & lg <= sm & Term[n1, n2]
  case {
    n1 = 0 -> requires n2 > 0 ensures xs::sll<n2, sm> & !res;
    n1 != 0 -> ensures xs::uls<n1-n, lg1, q> * q::sll<n2+n, lg> & lg1 <= lg & 0 < n <= n1;
  }
  */
  /*
  requires xs::ls<n1, _, lg, _, p> * p::sll<n2, sm> & lg <= sm
  case {
    n1 = 0 -> requires n2 > 0 ensures xs::sll<n2, sm> & !res;
    n1 != 0 -> ensures xs::ls<n1-n, _, lg1, _, q> * q::sll<n2+n, lg> & lg1 <= lg & 0 < n <= n1;
  }
  */
  /*
  requires xs::ls<n1, sm1, lg1, srt, p> * p::sll<n2, sm2> & lg1 <= sm2 & srt = 1
  case {
    n1 = 0 -> requires n2 > 0 ensures xs::sll<n2, sm2> & !res;
    n1 != 0 -> ensures xs::sll<n1+n2, sm1> & !res;
  }
  */
  
  requires xs::ls<n1, sm1, lg1, srt, p> * p::sll<n2, sm2> & lg1 <= sm2
  case {
    n1 = 0 -> requires n2 > 0 ensures xs::sll<n2, sm2> & !res;
    n1 != 0 -> case {
      srt = 1 -> ensures xs::sll<n1+n2, sm1> & !res;
      srt != 1 -> ensures 
        //xs::ls<n1-n, _, _, _, q> * q::sll<n2+n, _> & 0 < n <= n1 & res
        xs::ls<n1-1, _, _, _, q> * q::sll<n2+1, _> & res
        /* & lg1r <= lg1 */ /* & lg1r <= lg1 & sm2r <= sm2 & sm2r <= lg1 */;
    }
  }
  
  /*
  requires xs::ls<n1, sm1, lg1, srt, p> * p::sll<n2, sm2> & lg1 <= sm2
  case {
    n1 = 0 -> requires n2 > 0 ensures xs::sll<n2, sm2> & !res;
    n1 != 0 -> ensures 
      //xs::ls<n1-n, _, lg1r, _, q> * q::sll<n2+n, lg1> & lg1r <= lg1 & 0 < n <= n1 & (srt = 1 & !res | srt != 1 & res);
      xs::ls<n1-n, _, lg1r, _, q> * q::sll<n2+n, lg1> & lg1r <= lg1 & 0 < n <= n1 & srt != 1 & res or
      xs::sll<n1+n2, sm1> & srt = 1 & !res;
  }
  */
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

/*
void bsort(node xs)
  requires xs::ls<n1, sm1, lg1, srt, p> * p::sll<n2, sm2> & n1 + n2 > 0 & lg1 <= sm2  
  ensures xs::sll<n1+n2, _>;
{
  bool b;

  b = bubble(xs);
  if (b) {
    bsort(xs);
  }
}
*/
