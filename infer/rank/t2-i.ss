// CHOICE in Transition Invariant paper
//Termination: Contradiction in Phase Constraints.
//Termination checking result:
// Please use the same phase!

ranking ra(int x).
ranking rb(int x).
ranking r2(int x, int y).

bool rand()
  requires Term[]
  ensures true;

void loop1(int y, int x)
  infer @pre [ra,rb,r2]
 case {
     x>0 & y>0 ->
   case {
       x=y-1 -> requires Term[0,ra(x)] ensures true;
       x=y-2 -> requires Term[0,rb(x)] ensures true;
       ((x!=y-1) & (x!=y-2)) -> requires Term[1,r2(x,y)] ensures true;
      }
  x<=0 | y<=0 -> requires Term[] ensures true;
  }
{
  if (x>0 && y>0) {
    if (rand()) {
      y = x;
      x = x-1;
    } else {
      int t=x+1;
      x = y-2;
      y=t;
    }
    loop1(y,x);
  }
}

/*

!!! NEW RANK:[ 
 (1<=x) --> (ra(x))>=0,
 (1<=x) --> (rb(x))>=0,
 (1<=y & y<=x | 1<=x & x<=(y-3)) --> (r2(x,y))>=0,
 ==> ra[1]>=1
 ==> rb[1]>=1
 ==> r2[1]>=1,r2[2]>=1


 (x'=x-1 & 2<=x) --> (ra(x))>(ra(x')),
 (x'=x-1 & 2<=x) --> (ra(x))>(rb(x')),
 (x'=x-1 & 2<=x) --> (rb(x))>(ra(x')),
 (x'=x & 1<=x) --> (rb(x))>(ra(x')),
(y=x'+2 & x=y'-1 & 2<=y' & y'<=x' | y=x'+2 & x=y'-1 & 1<=x' & x'<=(y'-
  3)) --> (r2(x,y))>(r2(x',y'))]

  1. ra[1]->ra[1]:DEC(1)
  2. ra[1]->rb[1]:DEC(1)
  3. rb[1]->ra[1]:DEC(1)
  4. rb[1]->ra[1]:NC
  5. r2[1]->r2[2]:DEC(2),r2[2]->r2[1]:INC(1)

 */
