data node { int val; node next }

ll<n> ==
  self = null & n = 0 or
  self::node<v, p> * p::ll<n1> & n = n1 + 1
  inv n >= 0;

int length (node x)
  infer[@term]
  requires x::ll<n>
  ensures x::ll<n> & res=n;
{
  if (x == null) return 0;
  else return 1 + length(x.next);
}
/*
# tinf/data/ll1.ss

Why is there a "check 1 fail" message in the post branch?
What does it signify?

Checking procedure length$node... check 1 fail
Procedure length$node SUCCESS.

Note that in the ti3 branch, we got the following instead:

Checking procedure length$node...
Procedure length$node SUCCESS.

# ll1.ss --imm

int length (node x)
	infer[@term]
	requires x::ll<n>
        ensures x::ll<n> & res=n;

Not using integer n in termination analysis

Base/Rec Case Splitting:
[	length: [[2] 1<=x & x<=2@R,[3] x=0@B]
]
Termination Inference Result:
length:  requires x::ll<n> & truecase {
                          x=1 -> requires emp & Term[62,4]
 ensures x::ll<n_41> & n_41=n & 
                          res=n; 
                          x=2 -> requires emp & Term[62,5]
 ensures x::ll<n_41> & n_41=n & 
                          res=n; 
                          x=0 -> requires emp & Term[62,1]
 ensures x::ll<n_41> & n_41=n & 
                          res=n; 
                          }

*/
