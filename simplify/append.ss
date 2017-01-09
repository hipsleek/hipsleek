data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

void append(node xxx, node yyyy)
  requires xxx::ll<nnn> * yyyy::ll<mmm> & nnn>0
  ensures xxx::ll<eee>& eee=nnn+mmm;
{
  // dprint;
	node tmp = xxx.next;
	bool fl_bb = tmp != null;
	if (fl_bb) {
		append(xxx.next, yyyy);
                dprint;
		return;
	}
	else {
		xxx.next = yyyy;
                dprint;
		return;
	}
}

/*
# append.ss

--simpl-pure-part does not make any difference to the output
even when -dd is turned on or when we use -tp oc 

What are important program variables?
 - vars in pre-conditions
 - vars of parameters
 - vars of local variables (with scope)
 - bind variables (with scope)

When can simplification be done?
 - after check_exp(invocation?)

 State:(exists e_1436: x'::node<Anon_1418,q_1419> * q_1419::ll{}<e_1436>&0<=m_1431 & 0<=n_1430 & e_1436=m_1431+n_1430 & 0<=flted_7_1417 & 0<=m & m_1431=m & n_1430=flted_7_1417 & tmp_41'=q_1419 & flted_7_1417+1=n & x'=x & y'=y & 0<n & tmp_41'!=null & fl_42'&{FLOW,(4,5)=__norm#E}[]

bool     --> bool>0
not(bool)  --> not(bool>0)
x!=null --> x>0
x=null  --> x<=0

X := {[e_1436,q_1419,x,x',y,y',m,n,e,tmp_41',fl_42',Anon_1418]:
exists (m_1431,n_1430,flted_7_1417: 
0<=m_1431 & 0<=n_1430 & e_1436=m_1431+n_1430 & 0<=flted_7_1417 
& 0<=m & m_1431=m & n_1430=flted_7_1417 & tmp_41'=q_1419 
& flted_7_1417+1=n & x'=x & y'=y & 0<n & tmp_41'>0 
& fl_42'>0)

Omega simplify but need to consider x!=y or x!=0 etc

{[e_1436,q_1419,x,x,y,y,m,e_1436-m+1,e,q_1419,fl_42,Anon_1418]: 0 <= m <= e_1436 && 1 <= fl_42 && 1 <= q_1419}

*/
