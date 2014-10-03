int fact(int x)
  infer[@post_n]
 case {
  x=0 -> ensures res=1;
  x>0 -> ensures res>=1;
  x<0 -> requires false ensures false;
}
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact-case2.ss --pcp

why EList? Why missing ensures false?

static  EList :ECase case {
               x=0 -> EList :EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                                     EAssume 
                                       emp&res=1&{FLOW,(24,25)=__norm}[]

               ;
               0<x -> EList :EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                                     EAssume 
                                       emp&1<=res&{FLOW,(24,25)=__norm}[]

               ;
               x<0 -> EBase hfalse&false&{FLOW,(24,25)=__norm}[] 
               }


*/
