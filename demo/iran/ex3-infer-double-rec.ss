int double(int n)
  infer[@post_n]
  requires true
  ensures  true;
{
  if (n==0) return 0;
  else return 2+double(n-1);
}

/*
Post Inference result:
double$int
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           htrue&n>=0 & 2*n=res&{FLOW,(4,5)=__norm#E}[]
*/

