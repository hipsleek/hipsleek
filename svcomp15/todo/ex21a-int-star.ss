
data int_star {
  int val;
}


int alloc_data(int_star p)
{
  return p.val;
}


int main() 
{
  int_star addr_data = new int_star();
  r = alloc_data(addr_data);
  return r;
}
