/*
data int_star {
  int val;
}
*/

int alloc_data(int* p)
{
  return *p;
}


int main() 
{
  int data;
  int r=alloc_data(&data);
  return r;
}
