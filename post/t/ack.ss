int Ack(int m, int n)
infer [@term]
 requires true
 ensures true;
{ 
	if (m==0) return n+1;
	else if (n==0) {
		int m1 = m-1;
                //assert m'-m1'>0; //'
                //assert m1'>=0; //'
    return Ack(m1, 1);
  }
 	else {
		int m1=m-1;
   	int n1=n-1;
   	//assert m'=m' & /* n1'>=0 & */ n'-n1'>0; //'
   	int r = Ack(m, n1);
   	//assert m'-m1'>0 /* & m1'>=0 */; //'
   	return Ack(m-1, r);
 	}
}
/*
# ack.ss

Base/Rec Case Splitting:
[	Ack: [[4] m=0@B,[5] 1<=n & 1<=m@R,[6] n<=(0-1) & 1<=m@R,[7] m<=(0-1) & 1<=n@R,[8] n<=(0-1) & m<=(0-1)@R,[9] n=0 & 1<=m@R,[10] n=0 & m<=(0-1)@R]
]

// seems to take a very long time. Is it going into a Loop?
// can we print some intermediate results?
// can we have some upper bound cut-off?

Base/Rec Case Splitting:
[	Ack: [[4] m=0@B,[5] 1<=n & 1<=m@R,[6] n<=(0-1) & 1<=m@R,[7] m<=(0-1) & 1<=n@R,[8] n<=(0-1) & m<=(0-1)@R,[9] n=0 & 1<=m@R,[10] n=0 & m<=(0-1)@R]
]

*/

