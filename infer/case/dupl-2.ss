/* selection sort */

data node {
	int val; 
	node next; 
}


bool isNull(node x)
 case {
  x=null -> ensures res;
  x!=null -> ensures !res;
 }

void foo(node x)
  requires true
  ensures true;
{
  dprint;
  bool b=isNull(x);
  dprint;
}
/*
Why is x'=null duplicated. It seems to be added by 
ensures...

 Label: 
 State:or[emp&x=x' & x'=null & b_25' & x'=null&{FLOW,(22,23)=__norm}[]
          es_var_measures: MayLoop
; 
         emp&x=x' & x'!=null & !(b_25') & x'!=null&{FLOW,(22,23)=__norm}[]
         es_var_measures: MayLoop
]
 ]

Proving precondition in method isNull$node for spec:
 ((None,[]),ECase case {
                   x'=null -> ((None,[]),EBase emp&MayLoop&
                                               {FLOW,(1,25)=__flow}[]
                                                 EAssume 64::
                                                   emp&res & x'=null&
                                                   {FLOW,(22,23)=__norm}[])
                   ;
                   x'!=null -> ((None,[]),EBase emp&MayLoop&
                                                {FLOW,(1,25)=__flow}[]
                                                  EAssume 65::
                                                    emp&!(res) & x'!=null&
                                                    {FLOW,(22,23)=__norm}[])
                   
                   })


 */

