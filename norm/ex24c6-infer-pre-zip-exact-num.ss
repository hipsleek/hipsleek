
relation P(int x, int y).

int zip(int x,int y)
//  requires x>=0 & y>=0 & x<=y
 infer [P] 
 requires P(x,y) & x>=0 & y>=0 
 ensures true;
{
  if (x==0 && y==0) return x;
  else {
    int r=zip(x-1,y-1);
    return 1+r;
  }
}

/*
# ex24c6.ss

# can hip be fixed with new gfp procedure?

!!! **typechecker.ml#845:WARNING : Spurious RelInferred (not collected):[RELASS [P]: ( P(x,y)) -->  (x!=0 | 1>y),RELASS [P]: ( P(x,y)) -->  (y!=0 | 1>x),RELDEFN P: ( P(x,y) & x=v_int_12_1762'+1 & y=v_int_12_1761'+1 & 0<=v_int_12_1762' & 
 0<=v_int_12_1761') -->  P(v_int_12_1762',v_int_12_1761')]
Procedure zip$int~int SUCCESS.


!!! **pi.ml#686:lst_assume (after norm and postprocess):[( P(x,y), ((x!=0 & y!=0) | (x!=0 & 1>x) | (1>y & y!=0) | (1>y & 1>x)))]
!!! PROBLEM with fix-point calculation
ExceptionFailure("get_unchanged_fixpoint: Invalid rel")Occurred!


*/
