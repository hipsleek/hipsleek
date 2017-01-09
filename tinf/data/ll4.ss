data node { int val; node next }

ll<n> == 
	self = null & n = 0 or 
	self::node<v, p> * p::ll<n1> & n = n1 + 1
	inv n >= 0;

int length (node x)
	infer[@term]
	requires x::ll<n>@L 
	ensures res=n;
{
	if (x == null) return 0;
	else return 1 + length(x.next);
}
/*
# ll3.ss --pcp

   EBase exists (Expl)[](Impl)[n](ex)[]x::ll{}<n>@L&{FLOW,(24,25)=__norm}[]
           EBase emp&lengthpre_0(n)[62]&{FLOW,(24,25)=__norm}[]
                   EAssume 
                     emp&lengthpost_1176(n)[]&{FLOW,(24,25)=__norm}[]

Why @L not printed for inferred spec?

Why did we get x=1 and x=0 for node type?

Termination Inference Result:
length:  requires x::ll<n> & truecase {
                          1<=n -> requires emp & Term[62,3,-1+(1*
                          n)]
 ensures emp & true; 
                          n=0 -> requires emp & Term[62,1]
 ensures emp & true;

                          
                          x=0 -> requires emp & Term[62,1]
 ensures emp & true;

*/
