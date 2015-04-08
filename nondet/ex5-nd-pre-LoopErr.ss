pred_prim nondet<>
  inv true;

int nondeterm()
  requires true
  ensures res::nondet<>;

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures emp;
    i >=0 -> requires LoopErr ensures emp;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    foo(i);
    dprint;
  }
}

/*
# nondet/ex5-loop.ss
Adding true in post led to the following..

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures emp;
    i >=0 -> requires Loop ensures emp;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    foo(i);
    dprint;
  }
}

dprint(simpl): ex5-nd-param-LoopErrss:17: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:or[i'::nondet{}<>&i'<=(0-1) & 0<=i
    &{FLOW,(4,5)=__norm#E}[]
; 
         i'::nondet{}<>&0<=i' & 0<=i
    &{FLOW,(4,5)=__norm#E}[]
]

Let LoopErr denotes an error

  LoopErr |- LoopErr --> MayLoop

  LoopErr |- Loop --> MayLoop

  LoopErr |- * --> LoopErr

  Loop |- Loop --> MayLoop

  Loop |- * --> Loop

  MayLoop |- * --> MayLoop
 
         M>N
  -----------------------------
  Term M |- Term N --> Term M

  Term M |- * --> FAIL

*/
