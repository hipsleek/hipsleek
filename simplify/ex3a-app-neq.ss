data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;


void foo(node xxx, node yyyy)
  requires xxx::ll<nnn> & nnn>0
  ensures xxx::ll<nnn>;
{
  // dprint;
	node xxx = xxx.next;
	bool xxx_18 = xxx != yyyy;
	if (xxx_18) {
                dprint;
		return;
	}
	else {
		return;
	}
}

/*
# ex3a-app-new.ss (FIXED by Long)

renamed var xxx_18 clash with an existing var.
What should be done here?

do we need a pre-process to find all the vars?


void foo(node xxx, node yyyy)[]
static EBase: [][](emp ; (emp ; (xxx::ll{}<nnn>@M[HeapNode1]))) * ([] & nnn > 0)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; (xxx::ll{}<nnn>@M[HeapNode1]))) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: node xxx_18,boolean xxx_18
node xxx_18 = member access xxx~~>next
boolean xxx_18 = xxx_18 != yyyy
(100, ):if (xxx_18) { 
  (100, ):{dprint
(102, ):return };
} else { 
  (100, ):{(101, ):return }
}}
}



*/
