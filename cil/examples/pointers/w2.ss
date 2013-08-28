

int foo(int N) 
 requires N>=0
 ensures res=N;
{
 int i = 0;
 while (true) 
  requires i<=N
  ensures i'=N ;//'
  {
    if (i>=N) return i; 
    i = i+1;
  }

}


/*
expect:
loop
static  ((None,[]),EBase emp&i<=N&{FLOW,(23,24)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,26)=__flow}[]
                            EAssume 67::ref [i]
                              EXISTS(ot: eres::rExp<ot>@M[Orig]&N=i' & i'=ot&
                              {FLOW,(19,20)=rExp})[])
dynamic  EBase hfalse&false&{FLOW,(23,24)=__norm}

*/
