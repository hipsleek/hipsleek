
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
     infer [R]
     requires R(x,y,a,b)
     ensures true;
{

  if (x>0 || y>0) {
    x = x+a-b-1;
    y = y+b-a-1;
    a=a+1;
    a=a-1;
    loo(x,y,a,b);
  };
}

/*
# ex21a.ss -dre "analyse_param"

(==cformula.ml#1725==)
analyse_param@1
analyse_param inp1 :[( 
x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & (b'+x')<a' & b'<=(a'+y') & R(x,y,a',b'), R(x',y',a',b')),
( y=((a'+y')-b')+1 & x=(b'-a')+x'+1 & (a'+y')<b' & a'<=(b'+x') & R(x,y,a',b'), R(x',y',a',b')),
( x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & a'<=(b'+x') & b'<=(a'+y') & R(x,y,a',b'), R(x',y',a',b'))]
analyse_param inp2 :[(int,x),(int,y),(int,a),(int,b)]
analyse_param@1 EXIT:[[IND([x,b',a',x'], x=(b'-a')+x'+1),IND([y,a',y',b'], y=((a'+y')-b')+1),FLO(a'),FLO(b')],[IND([x,b',a',x'], x=(b'-a')+x'+1),IND([y,a',y',b'], y=((a'+y')-b')+1),FLO(a'),FLO(b')],[IND([x,b',a',x'], x=(b'-a')+x'+1),IND([y,a',y',b'], y=((a'+y')-b')+1),FLO(a'),FLO(b')]]

From this:
x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & (b'+x')<a' & b'<=(a'+y') 
  & R(x,y,a',b'), R(x',y',a',b')),

We need to extract:
 R(x,y,a',b') --> R(x',y',a',b')

And then using:
 x-->x'  with x=(b-a)+x'+1     
 y-->y'  with y=((a+y')-b)+1
 a-->a' with a=a'
 b-->b' with b=b'

After that, we re-arrange the formula to give:
 x-->x'  with x'=x-(b-a)-1     
 y-->y'  with y'=y-(a-b)-1
 a-->a' with  a'=a
 b-->b' with  b'=b

 Finally:
 x-->x'  with x'=IND(x-(b-a)-1)     
 y-->y'  with y'=IND(y-(a-b)-1)
 a-->a' with  a'=FLOW(a)
 b-->b' with  b'=FLOW(b)

 R(x,y,a',b') --> R(x',y',a',b')

For linear expressions, the above can be assisted by Omega, as shown
in ex21a1-param.oc. However, this may affect non-linear formula.

# oc ex21a1-param.oc

Rel := {[x,y,a,b]->[x',y',a',b']:a=a' & b=b' & x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & (b'+x')<a' & b'<=(a'+y')};

Rel1 := {[x,y,a,b]->[x',y',a',b']:exists(y',a',b':a=a' & b=b' & x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & (b'+x')<a' & b'<=(a'+y'))};

Rel1;
#{[x,y,a,b] -> [x+a-b-1,y',a',b'] : x <= 0 && 1 <= y}

Rel2 := {[x,y,a,b]->[x',y',a',b']:exists(x',a',b':a=a' & b=b' & x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & (b'+x')<a' & b'<=(a'+y'))};

Rel2;
#{[x,y,a,b] -> [x',y-a+b-1,a',b'] : x <= 0 && 1 <= y}

Rel3 := {[x,y,a,b]->[x',y',a',b']:exists(x',y',b':a=a' & b=b' & x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & (b'+x')<a' & b'<=(a'+y'))};

Rel3;
#{[x,y,a,b] -> [x',y',a,b'] : x <= 0 && 1 <= y}

Rel4 := {[x,y,a,b]->[x',y',a',b']:exists(x',y',a':a=a' & b=b' & x=(b'-a')+x'+1 & y=((a'+y')-b')+1 & (b'+x')<a' & b'<=(a'+y'))};

Rel4;
#{[x,y,a,b] -> [x',y',a',b] : x <= 0 && 1 <= y}


 */
