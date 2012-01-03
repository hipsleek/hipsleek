//Example from the slide of "The polyranking principles"
// Generalization of ex9.ss
void loop(ref int x, ref int y, int k, int N, bool b)
requires k>0
case {
	x>N -> variance [0,0] ensures "l1":x'=x & y'=y;
	x<=N -> case {
				//l3 -> l2 -> l1
				b -> case {
						y>N+1 -> //variance N-x
								 variance [0,1,N-x]
								 ensures "l2":true;
						y<=N+1 -> //variance (N+1)-y
	                variance [0,2,(N+1)-y]
								  ensures "l3":true;
					 }

				//l2 -> l1
				!b -> //variance N-x
            variance [0,3,N-x]
					  ensures "l2":true;
			}
}
{	
	if (x<=N) {
		if (b) {
			update1(x, y, k);

			assert "l2": (N-x')-(N-x)<0;
			assert "l2": N-x>=0;
			//assert "l2": N-x'>=0;

			assert "l3": (N+1-y')-(N+1-y)<0;
			assert "l3": true & (N+1-y'>=0 | y'>N+1); //bounded or l3->l2
		   
			loop(x, y, k, N, randBool());
		} else {
			update2(x, y);

			assert "l2": (N-x')-(N-x)<0;
			assert "l2": N-x>=0;
			//assert "l2": N-x'>=0;
			
			loop(x, y, k, N, randBool());
		}
	}
}

bool randBool()
  requires true
  ensures true;

//update (x,y) to (x',y') which 2*x'>=x+y-1 /\ y'=y+k
void  update1(ref int x, ref int y, int k)
requires true
ensures 2*x'>=x+y-1 & y'=y+k;

//update (x,y) to (x',y') which x'=x+1 /\ y'>=y
void update2(ref int x, ref int y)
requires true
ensures x'=x+1 & y'>=y;
