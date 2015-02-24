global int CNT=0;// this init seems useless

void countUp()
 requires true
 ensures CNT'=CNT+1;
/*
void countUp$int(  int CNT_16)
@ref CNT_16
static  EBase htrue&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [CNT_16]
                   emp&CNT_16'=1+CNT_16&{FLOW,(4,5)=__norm#E}[]
*/

void countDown()
 requires CNT>0
 ensures CNT'=CNT-1;
/*
void countDown$int(  int CNT_15)
@ref CNT_15
static  EBase emp&0<CNT_15&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [CNT_15]
                   emp&CNT_15'+1=CNT_15&{FLOW,(4,5)=__norm#E}[]

*/

void main ()
  requires true
  ensures CNT'=1;
{
  CNT = 0;
  dprint;
  countUp();
  countUp();
  countDown();
  dprint;
}
/*
void main$int(  int CNT_14)
@ref CNT_14
static  EBase htrue&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [CNT_14]
                   emp&CNT_14'=1&{FLOW,(4,5)=__norm#E}[]
{(((((CNT_14 = 0;
dprint);
{countUp$int(CNT_14)});
{countUp$int(CNT_14)});
{countDown$int(CNT_14)});
dprint)}
*/
