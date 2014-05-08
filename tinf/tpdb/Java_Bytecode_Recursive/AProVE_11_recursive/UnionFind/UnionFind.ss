data UnionFind {
  UnionFind parent;
}

lseg<n, p> == 
  self = p & n = 0 or
  self::UnionFind<q> * q::lseg<n - 1, p>
  inv n >= 0;

unionfind<n> == 
  self::lseg<n - 1, p> * p::UnionFind<p>
  inv n > 0;

lemma_safe self::lseg<n, r> <- self::lseg<m, q> * q::UnionFind<r> & n = m + 1;

void setParent(UnionFind x, UnionFind p)
  requires x::UnionFind<xp> * p::UnionFind<pp> & Term
  ensures x::UnionFind<p> * p::UnionFind<pp>;
{
  x.parent = p;
}

void makeSet(UnionFind x)
  requires x::UnionFind<_> & Term
  ensures x::UnionFind<x>;
{
  x.parent = x;
}

UnionFind find(UnionFind x)
  requires x::unionfind<n> & Term[n]
  ensures x::lseg<n - 1, res> * res::UnionFind<res>;
{
  if (x.parent == x)
    return x;
  else
    return find(x.parent);
}

void uni(UnionFind x, UnionFind y) 
  requires x::unionfind<n1> * y::unionfind<n2> & Term
  ensures x::lseg<n1, p> * y::lseg<n2 - 1, p> * p::UnionFind<p>;
{
  UnionFind xRoot = find(x);
  UnionFind yRoot = find(y);
  xRoot.parent = yRoot;
}

int rand()
  requires Term
  ensures res >= 0;

void main() 
  requires Term
  ensures true;
{
  UnionFind y = new UnionFind(null);
  makeSet(y);
  int i = 1;
  int j = rand();
  
  while (i < j) 
    requires y::unionfind<n>
    case {
      i >= j -> requires Term ensures y' = y;
      i < j -> requires Term[j - i] ensures y' = y;
    }
  {
    UnionFind x = new UnionFind(null);
    makeSet(x);
    uni(x, y);
    i++;
  }
}
