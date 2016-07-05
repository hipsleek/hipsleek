data node {
  int val;
  node next;
}

sll<v> == self::node<v,null>
  or self::node<v,q>*q::sll<w> & v<=w
  inv self!=null;


sll0<v,high> == self::node<v,null> & v=high
  or self::node<v,q>*q::sll0<w,h2> & v<=w & high=h2
  inv self!=null & v<=high;


sll2<low,high> == self=null & low<=high
  or self::node<v,q>*q::sll2<l2,h2> & low<=v<=l2 & h2<=high
  inv low<=high;


sll3<low,high> == self=null & low<=high
  or self::node<v,q>*q::sll3<l2,h2> & low=v & v<=l2 & h2<=high
  inv low<=high;

sll4<low> == self=null 
  or self::node<v,q>*q::sll4<l2> & low=v & v<=l2 
  inv true;


sll5<S> == self=null & S={} 
  or self::node<v,q>*q::sll5<S1> & S=union({v},S1) & forall(x:(x notin S1 |v<=x))
  inv true;


