int main(int n)
  requires true
  ensures res=n;
{
  int z=0;
  while (z!=n)
  case {
    z<=n -> requires Term[n-z]
            ensures z'=n; //'
    z>n -> requires Loop
           ensures false;
   } 
    {
      z=z+1;
    }
  return z;
}
