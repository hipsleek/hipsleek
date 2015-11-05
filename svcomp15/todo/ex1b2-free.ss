
data int_star {
  int val;
}

data TData {
  int_star lo;
}

void alloc_data(TData pdata)
{
  pdata.lo = new int_star(0);
}


int main() 
{
  TData data = new TData();
  alloc_data(data);
  int r =0;
  free(data);
  return r;
}
