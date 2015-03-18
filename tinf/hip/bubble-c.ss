/* bubble sort */

data node {
  int val;
  node next;
}

sll<n, sm> ==
  self::node<sm, null> & n=1 or	
  self::node<sm, q> * q::sll<n-1, qm> & q!=null & sm <= qm 
  inv n>=1;

ull<n, sm> ==
  self::node<sm, null> & n=1 or
  self::node<v, q> * q::ull<n-1, sm1> & sm = min(v, sm1) & q!=null
  inv n>=1;

lemma self::sll<n, sm> -> self::ull<n, sm>;

bool bubble(node xs)
  requires xs::ull<n, s> & Term[n]
  case {
    n=1 -> ensures xs::node<s, null> & !res;
    n!=1 -> ensures 
      xs::node<s, p> * p::ull<n-1, s1> & s <= s1 & res or
      xs::sll<n, s> & !res;
  }
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
  requires xs::ull<n, sm> & Term[n]
  ensures xs::sll<n, sm>;
{
  bool b;

  b = bubble(xs);
  if (b) {
    bsort(xs.next);
  }
}
