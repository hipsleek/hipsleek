data node { int val; node next }

ll<n> == 
	self = null & n = 0 or 
	self::node<v, p> * p::ll<n1> & n = n1 + 1
	inv n >= 0;

int length (node x)
	requires x::ll<n>@L
        ensures res=n;
{
	if (x == null) return 0;
	else return 1 + length(x.next);
}
/*
# ll2a.ss --imm

int length (node x)
	infer[@term]
	requires x::ll<n>@L
        ensures res=n;

Checking procedure length$node... Proving binding in method length$node for spec  EAssume 
   emp&{FLOW,(24,25)=__norm}[]
   , Line 10

( [(,1 ); (,2 )]) bind: node  x'::node<val_13_1183',next_13_1184'> cannot be derived from context
ll2a.ss_13:24_13:30



*/
