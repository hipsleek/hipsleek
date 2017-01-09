
relation P(int x, int y).

bool rand()
  requires true
  ensures res or !res;

int bsearch(int x,int y)
//  requires x>=0 & y>=0 & x<=y
 infer [P] 
 requires P(x,y) 
 ensures true;
{
  if (x==y) return 1;
  else {
    int m=(x+y)/2;
    if (rand()) return bsearch(x,m);
    else return bsearch(m+1,y);
  }
}

/*
# ex24c7a.ss

# can hip be fixed with new gfp procedure?

!!! **typechecker.ml#845:WARNING : Spurious RelInferred (not collected):[RELASS [P]: ( P(x,y)) -->  (x!=0 | 1>y),RELASS [P]: ( P(x,y)) -->  (y!=0 | 1>x),RELDEFN P: ( P(x,y) & x=v_int_12_1762'+1 & y=v_int_12_1761'+1 & 0<=v_int_12_1762' & 
 0<=v_int_12_1761') -->  P(v_int_12_1762',v_int_12_1761')]
Procedure zip$int~int SUCCESS.


!!! **pi.ml#686:lst_assume (after norm and postprocess):[( P(x,y), ((x!=0 & y!=0) | (x!=0 & 1>x) | (1>y & y!=0) | (1>y & 1>x)))]
!!! PROBLEM with fix-point calculation
ExceptionFailure("get_unchanged_fixpoint: Invalid rel")Occurred!


*/
