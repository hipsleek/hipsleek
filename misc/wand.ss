data node {
  int val;
  node next;
}

sumll<s> == self=null & s=0
  or self::node<v,q>*q::sumll<s-v>
  inv true;

sumls<p,s> == self=p & s=0
  or self::node<v,q>*q::sumls<p,s-v> 
  inv true;

/*
lemma_unsafe "xx" self::sumll<s> <-> (exists a,b: self::sumls<p,a> * p::sumll<b> & s=a+b);
*/

//lemma_safe "x2" self::sumll<s> -> self::sumls<self,0>*self::sumls<null,s>;

lemma_safe "x4" self::sumll<s> <- self::sumls<null,s>;

lemma_safe "x2" self::sumll<s> -> self::sumls<self,0>*self::sumls<null,s>;

lemma_safe "yy" self::sumls<p,s> <- (exists a,v: self::sumls<q,a> * q::node<v,p> & s=a+v);

int sumfn(node xs) 
  requires xs::sumll<s>@L
  ensures res = s;
{
  if (xs==null) return 0;
  else {
    return xs.val + sumfn(xs.next);
  }
}


void wloop(node ys, node@R xs, int@R sum) 
    requires ys::sumls<xs,sum>@L * xs::sumll<k>@L
    ensures  sum'=sum+k & xs'=null;  //
/*

  requires  (xs::sumll<k> --* ys::sumll<old>) * xs::sumll<k> & k+sum=old
  ensures  ys::sumll<sum'> & sum'=old & xs'=null;//'

    requires ys::sumls<xs,sum> * xs::sumll<k>
    ensures  ys::sumls<null,sum'> & sum'=sum+k & xs'=null;  
*/
{
  if (xs==null) return;
  else {
     sum = sum + xs.val;
     xs = xs.next;
     wloop(ys,xs,sum);
  }
}


int sumfnloop(node ys) 
  requires ys::sumll<s>@L
  ensures  res = s;
{
  node xs = ys;
  int sum = 0;
  wloop(ys,xs,sum);
  return sum;
}




