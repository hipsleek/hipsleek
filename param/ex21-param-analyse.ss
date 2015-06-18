
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
     infer [R]
     requires R(x,y,a,b)
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
# ex21.ss

This produced:

  x=(b'-a')+x'+1 & y=(y'-b')+a'+1 & a'<=(b'+x') & b'<=(y'+a') 
   & R(x,y,a',b') -->  R(x',y',a',b'),
  y=(y'-b')+a'+1 & x=(b'-a')+x'+1 & (y'+a')<b' & a'<=(b'+x') 
   & R(x,y,a',b') -->  R(x',y',a',b'),
  x=(b'-a')+x'+1 & y=(y'-b')+a'+1 & (b'+x')<a' & b'<=(y'+a') 
   & R(x,y,a',b')) -->  R(x',y',a',b')]

which seem sufficient to analyse that

   a,b are unchanged across recursion  a'=a, b'=b
   x,y are inductively changed by x'=nxt1(x); y'= nxt2(y)

# Add an option --analyse-param to trigger the output

  x,y are inductive
  a,b are unchanged

# more formally:

 parameter analysis for loo

 loo(x,y,a,b) = (IND([x,a,b],x+a-b-1)
                 ,IND([y,a,b],y+b-a-1)
                 ,FLOW(a)
                 ,FLOW(b))

# Earlier context were as follows. Are they similar to above?

  State:
      emp&a'=a & b'=b & y'=y & x=x' & 1<=y & R(x,y,a,b) & 1<=x'
    CtxOR
      emp&a'=a & b'=b & y'=y & x=x' & y<=0 & R(x,y,a,b) & 1<=x'&
    CtxOR
      emp&a'=a & b'=b & x=x' & y'=y & x'<=0 & 1<=y & R(x,y,a,b)&


 */
