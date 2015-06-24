relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
     infer [R]
     requires R(x,y,a,b)
     ensures true;
{

  if (x>0 || y>0) {
    x = x*a/b/2;
    y = y*b/a/2;
    loo(x,y,a,b);
  };
}

/*
# ex21i.ss

Raises "Not_found" somewhere when I try to run this.

 */
