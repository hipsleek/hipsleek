class Exp extends __Exc {
  int val;
}

void loop(ref int x)
  infer [@post_n]
  requires true
  ensures  true & flow __flow;
{
  if (x>0) {
    x = x-1;
    loop(x);
  } else {
    raise new Exp(2);
  }
}

/*
# ex3-bug (FIXED by always adding flow parameter)

Post Inference result:
loop$int
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [x]
           htrue&{FLOW,(1,30)=__flow#E}[]

Why inferred spec not capturing below:

!!! POST:  ((flow>=23 & 24>=flow & x>=1 & 0=x') | (flow>=23 & 24>=flow & 0>=x' & x'=x))


!!!  post_1358(x,x',flow) = ( x'=x & x<=0 & flow>=23 & flow<=24) \/ ( x_1378+1=x & 1<=x & post_1358(x_1378,x',flow))
!!! n_base:2
!!! bottom up
!!! bottom_up_fp:[( post_1358(x,x',flow), ((flow>=23 & 24>=flow & x>=1 & 0=x') | (flow>=23 & 24>=flow & 0>=x' & x'=x)))]
!!! fixpoint:[( post_1358(x,x',flow), ((flow>=23 & 24>=flow & x>=1 & 0=x') | (flow>=23 & 24>=flow & 0>=x' & x'=x)), true, true)]
!!! REL POST :  post_1358(x,x',flow)
!!! POST:  ((flow>=23 & 24>=flow & x>=1 & 0=x') | (flow>=23 & 24>=flow & 0>=x' & x'=x))
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
loop$int
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [x]
           htrue&{FLOW,(1,30)=__flow#E}[]

*/
