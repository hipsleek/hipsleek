/*

  Create a list of fractional cells.

 */

data cell{ int val;}

data cellNode{
  cell v;
  cellNode next;
}

/* A list of fractional cells */
cellList<n,M> == self=null & n=0
  or self::cellNode<v,p> * v::cell(1/M)<_> * p::cellList<n-1,M>
  inv n>=0;

// helper function to help split a cell into suitable form
cell getFrac(cell x, int M)
  requires x::cell(f)<_> & f>=1/M
  ensures x::cell(f-1/M)<_> * res::cell(1/M)<_> & res=x;

cellNode helper(cell x, int n, int M)
  requires x::cell(f)<_> & f=n/M & M>=n & n>=0
  ensures res::cellList<n,M>;
{
  if (n<1){return null;}
  else{
    cell fracCell = getFrac(x,M);
    int n1 = n-1;
    cellNode p = helper(x,n1,M);
    cellNode node = new cellNode(fracCell,p);
    return node;
  }
}

cellNode createCellList(cell x, int n)
  requires x::cell<_> & n>0
  ensures res::cellList<n,n>;
{
  return helper(x,n,n);
}
