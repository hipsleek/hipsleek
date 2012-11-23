data node {
  int val;
  node next;
}

data tree {
  tree left;
  tree right;
}

treelseg<t,p,d,h> == t::node<d,p> & self=null & h=0 
  or self::tree<left,right>*left::treelseg<t,r,d+1,h1>*right::treelseg<r,p,d+1,h2>
  & h = 1+max(h1,h2)
  inv h>=0;


 bool is_empty(node x)
  case {
    x=null -> ensures res;
    x!=null -> ensures !res;
 }

 int hd(node x)
   requires x::node<i,_>@I
   ensures res=i;

 void pop(ref node x)
   requires x::node<_,y>@I
   ensures x'=y;  //' removes a node
