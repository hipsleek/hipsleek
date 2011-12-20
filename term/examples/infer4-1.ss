int f_1 (int n)

{
	if (n==0) 
		return 0;
	else
		return f_1(n-1);
}

/*
1. Base case: n=0
2. Recursive case: n!=0
	 n!=0 |- f(n) > f(n-1) (1)
   n=0  |- f(n) >= lb    (2)
	 n!=0 |- f(n) >= lb    (3)
		
	 (1) ==> f(n) = n ()
   (2) Infer [lb] n=0 |- n>=lb ==> lb<=0
	 (3) Infer [n] n!=0 & lb<=0 |- n>=lb ==> n>=1

	 The candidate variance [n] is only possibly well-founded 
   under the condition n>=1. 
	 - Need to prove n<0 (not (n>=1 \/ n=0)) is the condition 
	 of non-terminating:
			n<0 & n'=n-1 |- n'<0: Valid
3. Check coverage and reachability to confirm the validity
   of the candidate variance [n] (using MAY/MUST analysis)			 
			n>=1 & n'=n-1 |- n'>=1: MAY
			n>=1 & n'=n-1 |- n'=0 : MAY
      n>=1 & n'=n-1 |- n'<0 : INVALID

			n<0 & n'=n-1 |- n'<0  : VALID

4. Refine specification for termination by calculating
	 the transition of program states:
	 case {
	 		n=0  -> Variance (0)      // Term Base_case
      n>=1 -> Variance (1) [n]  // Term [n]
      n<0  -> Variance (-1)     // NonTerm
	 }
*/

int f_2 (int n)

{
	if (n==5)
		return 0;
	else
		return f_2(n+1);
}

/*
1. Base case: n=0
2. Recursive case: n!=0
	 n!=0 |- f(n) > f(n+1) (1)
   n=0  |- f(n) >= lb    (2)
	 n!=0 |- f(n) >= lb    (3)
		
	 (1) ==> f(n) = -n
   (2) Infer [lb] n=0 |- -n>=lb ==> lb<=0
	 (3) Infer [n] n!=0 & lb<=0 |- -n>=lb ==> n<=-1
*/

int f_3 (int n)

{
	if (n==0)
		return 0;
	else
		return f_3(n-2);
}

/*
An example for the case of candidate variance refinement
by the reachability analysis
1. Base case: n=0
2. Recursive case: n!=0
	 n!=0 |- f(n) > f(n-2) (1)
   n=0  |- f(n) >= lb    (2)
	 n!=0 |- f(n) >= lb    (3)
		
	 (1) ==> f(n) = n ()
   (2) Infer [lb] n=0 |- n>=lb ==> lb<=0
	 (3) Infer [n] n!=0 & lb<=0 |- n>=lb ==> n>=1

	 The candidate variance [n] is only POSSIBLY well-founded 
   under the condition n>=1. 
3. Check coverage and reachability to confirm the validity
   of the candidate variance [n] (using MAY/MUST analysis)			 
			n>=1 & n'=n-2 |- n'>=1: MAY
			n>=1 & n'=n-2 |- n'=0 : MAY
      n>=1 & n'=n-2 |- n'<0 : MAY

			n<0 & n'=n-1 |- n'<0  : VALID

4. Refine specification for termination by calculating
	 the transition of program states:
	 case {
	 		n=0  -> Variance (0)      // Term Base_case
      n>=1 -> Variance MayTerm  // MayTerm
      n<0  -> Variance (-1)     // NonTerm
	 }

*/
