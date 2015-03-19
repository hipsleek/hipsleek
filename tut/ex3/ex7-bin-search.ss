bool rand()
  requires Term
  ensures true;


int bsearch(int i, int j)
  case {
    j<=i -> requires Term ensures true;
    j>i -> requires Term[j-i] ensures true;
  }
{
  if (i>=j) return i;
  int mid = (i+j)/2;
  if (rand()) return bsearch(i,mid);
  return bsearch(mid+1,j);
}
