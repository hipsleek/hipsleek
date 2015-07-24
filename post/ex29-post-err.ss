
void loo (ref int x, ref int y,int a, int b)
     infer [@post_n]
     requires true
     ensures true;
{

  if (x>0 || y>0) {
    //dprint;
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex29.ss


 */
