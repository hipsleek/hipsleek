
data node {
  int val;
  node next;
  }

istream<> == self::node<v,q>*q::istream<>
  inv true;

/*
multpred<ys,rs> ==
  self::node<a,qs> * ys::node<b,rs> * rs::node<a*b,ks> * qs::multpred<rs,ks> 
  inv true; 
*/
node mult(node xs, node ys)
  requires xs::istream<>@L * ys::istream<>@L
  ensures res::istream<>;
{ 
  return new node(xs.val*ys.val, mult(xs.next, ys.next));
}

/*
below<node ys> ==
  self::node<a,qs>*ys::node<b,rs> 
 case { a=b  -> [] qs::below<rs>;
      a!=b -> [] a<b;
  }
inv true;
*/
