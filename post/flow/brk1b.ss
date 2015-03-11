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

With --en-split-fixcalc:

((x'=2001 & 1<=x & x<=2000) | (x=x' & 2001<=x') | (x=x' & x'<=0))

 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [x]
      ((x'=2001 & 1<=x & x<=2000) 
      | (x'=2001 & 1998<=x & x<=2001) 
      | (x=x' & 2001<=x') 
      | (x=x' & x'<=0))&
           {FLOW,(4,5)=__norm#E}[]


Without --en-split-fixcalc:

 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [x]
           htrue&
   ((2000>=x & 2001=x') 
   | (x'>=2001 & x'=x) 
   | (0>=x' & x'=x))&
 {FLOW,(4,5)=__norm#E}[]

*/
