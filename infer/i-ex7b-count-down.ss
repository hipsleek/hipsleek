bool rand()
  requires Term
  ensures true;

relation P(int i, int j).
  relation Q(int i, int j,int r).


int foo(int i, int j)
  infer[P,Q]
  requires P(i,j)
  ensures Q(i,j,res);
{
  if (i>=j) return 0;
  int r = 2+foo(i+1,j);
  return r;
}

/*
# i-ex7b.ss

int foo(int i, int j)
  infer[P,Q]
  requires P(i,j)
  ensures Q(i,j,res);
{
  if (i>=j) return 0;
  int r = 2+foo(i+1,j);
  return r;
}

// ann_2
*************************************
******pure relation assumption 1 *******
*************************************
[RELDEFN P: ( i=v_int_15_1413'-1 & v_int_15_1413'<=j' & P(i,j')) -->  P(v_int_15_1413',j'),
RELDEFN Q: ( res=0 & j<=i & P(i,j)) -->  Q(i,j,res),
RELDEFN Q: ( res=v_int_15_1463+2 & i<j & Q(1+i,j,v_int_15_1463) & P(i,j)) -->  Q(i,j,res)]
*************************************
!!! **pi.ml#725:sp:compute_fixpoint:[( res=v_int_15_1463+2 & i<j, Q(i,j,res)),( res=0 & j<=i, Q(i,j,res))]
!!! **pi.ml#726: Q(i,j,res) = ( res=v_int_15_1463+2 & i<j) \/ ( res=0 & j<=i)
!!! **pi.ml#731:bottom_up_fp0:[( Q(i,j,res), ((exists(v_int_15_1463:res=v_int_15_1463+2) & i<j) | (res=0 & j<=i)))]

Post Inference result:
foo$int~int
 EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&(i<j | (res=0 & j<=i))&{FLOW,(4,5)=__norm#E}[]


// default
*************************************
[RELDEFN P: ( i=v_int_15_1413'-1 & v_int_15_1413'<=j' & P(i,j')) -->  P(v_int_15_1413',j'),
RELDEFN Q: ( res=0 & j<=i & P(i,j)) -->  Q(i,j,res),
RELDEFN Q: ( res=v_int_15_1463+2 & i<j & Q(1+i,j,v_int_15_1463) & P(i,j)) -->  Q(i,j,res)]
*************************************

!!! **pi.ml#613: Q(i,j,res) = ( res=v_int_15_1463+2 & i<j & Q(1+i,j,v_int_15_1463)) \/ ( res=0 & j<=i)

Post Inference result:
foo$int~int
 EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&res>=0 & (res+(2*i))>=(2*j)&{FLOW,(4,5)=__norm#E}[]

*/
