data node {
  int val;
  node next;
}


ll<n,a1,a2> == self=null & n=0 or
  self::node<_@a1,q@a2>*q::ll<n-1,a1,a2>
  inv n>=0;

int get(node x) 
  requires x::node<v,q>
  ensures  x::node<v,q> & res=v;  
{
  dprint;
  //x::node<v,q>
  return x.val;
  //x::node<v,q> & res=v
  dprint;
}


void sset(node x, int v)
  requires x::node<_,q>
  ensures  x::node<v,q>;
{
  x.val = v;
}

int getA(node x) 
  requires x::node<v@L,_@A>
  ensures  res=v;  
{
  return x.val;
}


void setA(node x, int v)
  requires x::node<_@M,_@A>
  ensures  x::node<v@M,_@A>;
{
  x.val = v;
}

void non_negative(node z)
  requires z::ll<n,@M,@L>
  ensures  z::ll<n,@M,@A>;
{
  if (z == null) return;
  else{
    int v = getA(z);
    if (v<0)  setA(z,(0-v));
  }
  non_negative(z.next);
}
