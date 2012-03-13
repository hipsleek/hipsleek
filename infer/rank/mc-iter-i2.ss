// Cristian solved this problem for iterative
// McCarthy after doing a trace!!

int mcCarthy (int x)
//requires x<=111
case {
	x>100 -> requires Term[] ensures res=x-10;
	x<=100 -> requires Term[] ensures res=91;
}
{
	int c = 1;
	loop(x, c);
	return x;
}

    /*
      case {
      x>100 -> requires MayLoop ensures x'=91 & c'=0 ;
      x<=100 -> requires MayLoop ensures x'=91 & c'=0 ;
	 }
    */
ranking r1(int x, int c).
ranking r2(int x, int c).

void loop (ref int x, ref int c)
infer @pre [r1,r2]
case {
  c<=0 -> requires Term[0] ensures x'=x & c'=c ;
    c=1 ->
      case {
      x>100 -> requires Term[1] ensures x'=x-10 & c'=0 ;
      x<=100 -> requires Term[2,r1(x,c)]  ensures x'=91 & c'=0 ;
        }
    c>1 -> 
      requires x<=111 & Term[2,r2(x,c)]
      ensures x'=91 & c'=0;
}
{
	if (c > 0) {
		if (x > 100) {
			x = x - 10;
			c--;
		} else {
			x = x + 11;
			c++;
		}
		loop(x, c);
	}
}
/*

mc-iter-i2.ss

Bounded
=======
c=1 & x<=100) -->  (r1(x,c))>=0, 
( x<=111 & 2<=c) -->  (r2(x,c))>=0, 

Transition
==========
( c=1 & c'=2 & x=x' - 11 & x'<=111) -->  (r1(x,c))>(r2(x',c')), 
( c=2 & c'=1 & x'=x - 10 & 101<=x & x<=110) -->  (r2(x,c))>(r1(x',c')), 
( x=x'+10 & c'=c - 1 & 91<=x' & x'<=101 & 3<=c) -->  (r2(x,c))>(r2(x',c')), 
( x=x' - 11 & c'=c+1 & x'<=111 & 2<=c) -->  (r2(x,c))>(r2(x',c'))]

Analysis:

(c=1 & x<=100) -->  (r1(x,c))>=0, 
  ==>  r1[1]<=100, r1[2]=1 
( x<=111 & 2<=c) -->  (r2(x,c))>=0, 
  ==>  r2[1]<=111, r1[2]>=2 
 
 1: r1(x,c)->r2(x',c') [r1[1]->r2[1]:NC; r1[2]->r2[2]:INC(1)]
 2: r2(x,c)->r1(x',c') [r2[1]->r1[1]:DEC(10); r2[2]->r1[2]:DEC(1)]
 3: r2(x,c)->r2(x',c') [r2[1]->r2[1]:INC(10); r2[1]->r2[1]:DEC(1)] 
 4: r2(x,c)->r1(x',c') [r2[1]->r1[1]:DEC(11); r2[2]->r1[2]:INC(1)]

   P(w*) -> C2

   infer[w*] D |- C. 
             x<y & P(y,z)  |- x < z
   infer[y,z] x<y |- x<z.

   D & P(..) --> C


*/
