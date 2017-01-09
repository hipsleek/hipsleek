int fact(int x)
 case {
  x=0-> ensures res=1;
  x>=0 -> ensures res>=1;
  //x<0 -> requires false ensures false;
}
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact-case5.ss --pcp

Exception occurred: Failure("the guards are not disjoint :  EList :ECase case {\n               x=0 -> EList :EAssume \n                               emp&res=1&{FLOW,(24,25)=__norm}[]\n                                ;\n               0<=x -> EList :EAssume \n                                emp&1<=res&{FLOW,(24,25)=__norm}[]\n                                 \n               }\n")

*/
