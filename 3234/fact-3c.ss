relation facta(int n, int f).
axiom n=0 ==> facta(n,1).
axiom n > 0 & facta(n-1,f1) ==> facta(n,n*f1).

int fact(int y, int z, int n)
  requires y>0 & n>=0 // //facta(z,y)
  ensures res>0; //facta(n,res);
{
  while (z!=n)
   case {
    z>n -> ensures false;
    z<=n -> requires y>0  //& facta(z,y)  
            ensures z'=n & y'>0 ; //& facta(n,y'); //' 
    }
    {
      z=z+1;
      y=y*z;
    }
  return y;
}

