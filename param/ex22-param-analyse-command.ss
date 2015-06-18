//relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
     infer [@analyse_param]
     requires true 
     ensures true;
{

  if (x>0 || y>0) {
    dprint;
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex22.ss

This is a command to analyse the parameters of a self-recursive
funtion. It should produce infer in ex21.ss; and later
mention that
  x,y are inductive
  a,b are unchaged
This info should later be attached to proc_decl

*/
