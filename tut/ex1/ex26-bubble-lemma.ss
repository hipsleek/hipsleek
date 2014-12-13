data node {
  int val;
  node next;
}

lsort<S> == emp & self=null & S={}
  or self::node<v,q>*q::lsort<S1> & S=union({v},S1)
          & forall (w:(w notin S1| v<=w))
  inv true;

ll<S> == emp & self=null & S={}
  or self::node<v,q>*q::ll<S1> & S=union({v},S1)
  inv true;

lemma_safe "lsort2ll" self::lsort<S> -> self::ll<S>;

lemma_safe "ll2lsort"self::lsort<S> <- self::ll<S>;

bool bubble(node xs)
	requires xs::ll<S> & xs!=null
	ensures xs::lsort<S> & !res
		or  xs::ll<S> & res;
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
	requires xs::ll<S> & xs!=null
	ensures xs::lsort<S>;
{
	bool b;

	b = bubble(xs);
	if (b) {
		bsort(xs);
	}
}



