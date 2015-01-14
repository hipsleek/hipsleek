int fact(int x)
 infer [@term]
 case {
  x>=0 -> ensures res>=1;
  //x<0 -> ensures res>=1;
}
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact-case.ss

automatically insert requires true ensure false
for missing case ..

static  EList :ECase case {
               0<=x -> EList :EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                                      EAssume 
                                        emp&1<=res&{FLOW,(24,25)=__norm}[]
                                        
               ;
               x<=(0-
               1) -> EBase emp&{FLOW,(24,25)=__norm}[]
                             EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                                     EAssume 
                                       hfalse&false&{FLOW,(24,25)=__norm}[]
                                        
               }
*/
