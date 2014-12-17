bool rand()
  requires true
  ensures res or !res;


int bsearch(int i, int j)
  infer [@pre_n,@post_n,@term]
  requires true
  ensures true;
{
  if (i>=j) return i;
  int mid = (i+j)/2;
  if (rand()) return bsearch(i,mid);
  return bsearch(mid+1,j);
}

/*
# ex7-bin-search.ss

 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           htrue&(i<j | (i=res & j<=res))&{FLOW,(4,5)=__norm#E}[]

@loop, is this correct?

Termination Inference Result:
bsearch:  requires true & truecase {
                      j<=i -> requires emp & Term[12,1]
     ensures true & (i<j | 
                      (i=res & j<=res)); 
                      ((i=0-3 & 5<=j & j<=20) | ((0-3)<=i & i<=(j-24)) | ((j-
                      2)<=i & i<j & 2<=j) | (i<=(0-1) & i<=(0-j) & 0<=j) | 
                      (((0-i)+1)<=j & j<=((0-(6*i))-14) & j<=((0-(2*i))+
                      2)) | (i<=(0-4) & 3<=((2*i)+j)) | (i<j & 
                      j<=1)) -> requires emp & MayLoop[]
     ensures true & (i<j | 
                      (i=res & j<=res)); 
                      }

*/
