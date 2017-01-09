data node2 {
  int val;
  node2 left;
  node2 right;
}

tree<h> == emp & self=null & h=0
  or self::node2<_,p,q>*p::tree<h1>*q::tree<h2> & h=1+max(h1,h2)
  inv h>=0;


int max2(int x,int y)
  requires true
  ensures res=max(x,y);

int height(node2 x)
  requires x::tree<h>
  ensures x::tree<h> & res=h;
{
  if (x==null) return 0;
  else {
    return 1+max2(height(x.left),height(x.right));
  }
}

avl<h> == emp & self=null & h=0
  or self::node2<_,p,q>*p::avl<h1>*q::avl<h2> & h=1+max(h1,h2)
  & -1<=h1-h2<=1 // near balanced property..
  inv h>=0;

