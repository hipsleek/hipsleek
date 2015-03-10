int main(int x)
  requires true
  ensures true;
{
  while (x > 0)
    infer [@post_n]
      requires true
      ensures true;
    {
      if (x > 2000) {
        break;
      } else {
        x = x + 1;
      }
    }
  return 0;
}

/*
# post/flow/ex1

It seems that dis-split-fixcalc is more precise
than en-split fixcalc. Is this correct?

# see ex1a.oc

With --dis-split-fixcalc:

 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [x]
      ((x'=2001 & 1<=x & x<=2000) 
      | (x'=2001 & 1998<=x & x<=2001) 
      | (x=x' & 2001<=x') 
      | (x=x' & x'<=0))&
           {FLOW,(4,5)=__norm#E}[]


--en-split-fixcalc:

 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [x]
           htrue&
   ((2000>=x & 2001=x') 
   | (x'>=2001 & x'=x) 
   | (0>=x' & x'=x))&
 {FLOW,(4,5)=__norm#E}[]

*/
