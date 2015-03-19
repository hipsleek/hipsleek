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
	node tmp = xxx.next;
	bool fl_bb = tmp != yyyy;
	if (fl_bb) {
                dprint;
		return;
	}
	else {
		return;
	}
}

/*
# ex3-app-new.ss

!!! **cfout.ml#423:important variables:[fl_47,tmp_46,nnn,xxx,yyyy,xxx',Anon_1507,q_1508,flted_7_1506]
!!! **cfout.ml#425:exists variables:[fl_47',yyyy',tmp_46']

# Why did we use fl_47 when the variable is fl_bb?
# Why wasn't fl_47' kept since it is an important variable.

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:xxx'::node<Anon_1507,q_1508> * q_1508::ll{}<flted_7_1506>
 & fl_47' & tmp_46'!=yyyy' & 0<nnn & yyyy'=yyyy 
 & xxx'=xxx & flted_7_1506+1=nnn & tmp_46'=q_1508
&{FLOW,(4,5)=__norm#E}[]

 ]

dprint after: ex3-app-neq.ss:19: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:xxx'::node<Anon_1507,q_1508> * q_1508::ll{}<flted_7_1506>
 &xxx=xxx' & nnn=1+flted_7_1506 & 0<=flted_7_1506 
 & yyyy!=q_1508
 &{FLOW,(4,5)=__norm#E}[]


*/
