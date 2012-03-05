int main(int n)
  requires true
  ensures res=n;
{
  int z;
  while (z!=n)
  case {
    z<=n -> ensures z'=n; //'
    z>n -> ensures false;
     } 
    {
      z=z+1;
    }
  return z;
}
