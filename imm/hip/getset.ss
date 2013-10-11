data node {
  int val;
  node next;
}


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
  dprint;
  //x::node<annon,q> fires: 
  //x::node<annon,q> |- x'::node<newv1,newv2> ====> S:  x'::node<newv1,newv2> & x=x'& newv1=v & newv2=q
  node tmp;
  tmp = x.next;
  x.next = null;
  x.next = tmp;
  x.val = v;
  //x::node<newvar,q> & newvar = v |- x::node<v,q>
  dprint;
}





int getA(node x) 
  requires x::node<v@L,_@A>
  ensures  res=v;  
{
  dprint;
  //x::node<v@L,_@A>
  return x.val;
  //x::node<v@[@L],_@A> * x::node<v@A,_@A> & res=v
  dprint;
}
//emp & res=v


void setA(node x, int v)
  requires x::node<_@M,_@A>
  ensures  x::node<v@M,_@A>;
{
  //x::node<annon,q> fires: 
  //x::node<annon,q> |- x'::node<newv1,newv2> ====> S:  x'::node<newv1,newv2> & x=x'& newv1=v & newv2=q
  dprint;
  x.val = v;
  dprint;
  //x::node<newvar,q> & newvar = v |- x::node<v,q>
}
