//Example from the slide of "The polyranking principles"

void loop(ref int x, ref int y, int k, int N, bool b)
requires k>0
case {
	x>N -> ensures "l1":x'=x & y'=y;
	x<=N -> case {
				//l3 -> l2 -> l1
				b -> case {
						y>N+1 ->	variance (1) [N-x]
									ensures "l2":true;
						y<=N+1 ->	variance (2) [(N+1)-y]
									ensures "l3":true;
					 }

				//l2 -> l1
				!b -> variance (1) [N-x]
					  ensures "l2":true;
			}
}
{	
	if (x<=N) {
		if (b) {
			update1(x, y, k);

			loop(x, y, k, N, randBool());
		} else {
			update2(x, y);

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
