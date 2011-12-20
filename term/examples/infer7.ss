//Variance inference for heap manipulating programs

data node { int val; node next; }

ll1<n> == 
	self=null & n=0 or
	self::node<_, r> * r::ll1<n-1>
	inv n>=0;

ll2<s> ==
	self=null & s=0 or
	self::node<v, r> * r::ll2<s1> & s=s1+v
	inv true;

int size (node x)
	//infer [x]
	//requires x::ll1<n>
	requires true
	ensures true;
{
	if (x==null)
		return 0;
	else {
		int s = size(x.next);
		dprint;
		return 1 + s;
	}
}

/*
1. Let f(x) be the variance measure of the size function.

2. Determine base case and loop case
	- Base case: x=null
	- Loop case: x!=null

3. Constraints for f(x); these constraints must be satisfied
with the inferred variance
	x!=null |- f(x) > f(x.next) (1)
	x!=null |- f(x) >= l_bnd    (2)
	x=null  |- f(x) >= l_bnd    (3)

	The LHS of the constraints is obtained from the given
	pre-condition (which might be true) and the symbolic execution.

4. Find suitable data structures for node x, that can help
the constraints (1), (2) and (3) to be satisfied.
	(1) <-> x!=null |- f(x) > f(r)

	There are two predicates that can be possibly matched with x
	(based on the facts that x is a node and x is not null):
	(a) ll1<n>
			x::ll1<n> & x!=null == x::node<v, r> * r::ll1<n1> & n=n1+1
			f(x) > f(r) == f(ll1<n>) > f(ll1<n-1>)
			(x and r is the RHS must be substituted by the same predicate???)
			Here, the argument n of the predicate ll1 decreases
			=> It can be a potential variance measure:
				 f(ll1<n>) = n
	(b) ll2<s>
			x::ll2<s> & x!=null == x::node<v, r> * r::ll2<s1> & s=s1+v
			f(x) > f(r) == f(ll2<s>) > f(ll2<s1>)
			s can be used as a variance measure; however,

					s=s1+v |- s>s1

			is not valid. We need to strengthen the LHS by the inference

					Infer [v] s=s1+v |- s>s1 ==> v>=1 

			- The predicate ll2 can be strengthened by the condition v>=1 
			to ensure the termination
			- How do we know v need to be inferred?

5. Infer the lower bound l_bnd
	 (a) f(ll1<n>) = n
			 (2) x::ll1<n> & x!=null |- n >= l_bnd
					 Infer [n] x::ll1<n> |- x!=null ==> n>=1
			 (3) x::ll1<n> & x=null  |- n >= l_bnd
					 Infer [n] x::ll1<n> |- x==null ==> n=0
			 ==> l_bnd = 0

	 (b) f(ll2<s>) = s
			 Refined predicate 
			 ll2<s> ==
				 self=null & s=0 or
				 self::node<v, r> * r::ll2<s1> & s=s1+v & v>=1
				 inv true;

			 (2) x::ll2<s> & x!=null |- s >= l_bnd
					 Infer [s] x::ll2<s> |- x!=null ==> s>=1 | s<=-1
			 (3) x::ll2<s> & x=null  |- s >= l_bnd
					 Infer [s] x::ll2<s> |- x=null ==> Fail (It should be s=0)
			 ==> l_bnd = 0

*/

















