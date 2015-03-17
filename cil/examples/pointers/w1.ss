

int foo(int N) 
 requires N>=0
 ensures res=N & N>=0;
{
int i = 0;
int oldN = N;
while (i < N) 
  requires i<=N
  ensures i'=N ;
  {
    i = i+1;
  }
 assert oldN'=N;
 dprint;
 return i;

}

/*
 read-only variables should be translated
 to pass-by-value rather than pass-by-ref

void f_r_500_while_8_0$int~int(  int i_26,  int N) rec
static  ((None,[]),EBase emp&i_26<=N&{FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 68::ref [i_26;N]
                              emp&N=i_26'&{FLOW,(22,23)=__norm}[])
dynamic  EBase hfalse&false&{FLOW,(22,23)=__norm}[]

*/

