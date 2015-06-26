
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
//infer [@post_n]
     requires true
  ensures y<=0 & x<=0 & y=y' & x=x' | y'<=0 & x'<=0 & y+x>=2+y'+x';
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

 EBase 
   htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     ref [x;y]
     htrue&
     ((0>=y & 0>=x & y=y' & x=x') | (0>=y' & 0>=x' & (y+x)>=(2+y'+x'))) &
     {FLOW,(4,5)=__norm#E}[]


 */
