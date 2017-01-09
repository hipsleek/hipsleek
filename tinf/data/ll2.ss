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
# ll2.ss --imm

int length (node x)
	infer[@term]
	requires x::ll<n>@L
        ensures res=n;

Why is there a bind failure? WHy wasn't @L used?

( [(,1 ); (,2 )]) bind: node  x'::node<val_14_1184',next_14_1185'> cannot be derived from context
ll2.ss_14:24_14:30

id: 6; caller: []; line: 14; classic: false; kind: BIND; hec_num: 1; evars: []; infer_vars: [@term ]; c_heap: emp
 checkentail (exists v1,p1,n1: x::node<v1,p1>@L * p1::ll{}<n1>@L&n=1+n1 & x!=null & 
!(v1') & v2'=1 & lengthpre_0(x)[62]&{FLOW,(24,25)=__norm})[]
 |-  x'::node<val1',next1'>&{FLOW,(1,27)=__flow}[]. 


*/
