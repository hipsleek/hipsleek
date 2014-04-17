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
  requires x::cell(f)<_>
  ensures x::cell(f-1/M)<_> * res::cell(1/M)<_> & res=x & f>=1/M
     or res=x & f=0.0;

cellNode helper(cell x, int n, int M)
  case{
    n=0 -> ensures res=null;
    n>0 -> requires x::cell(f)<_> & f=n/M & M>=n ensures res::cellList<n,M>;
  } //this spec is more precise (not allow f=0.0)
  /* requires x::cell(f)<_> & f=n/M & M>=n & n>=0 */
  /* ensures res::cellList<n,M> & n>0 or res=null & n=0; */
{
  if (n<=0){return null;}
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
