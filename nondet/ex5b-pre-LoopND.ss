pred_prim nondet<>
  inv true;

int nondeterm()
  requires true
  ensures res::nondet<>;

bool nondet_bool()
  requires true
  ensures res::nondet<>;

void foo(int x) 
  case {
    x >=0 -> requires Loop/* ND */  ensures emp;
    x < 0 -> requires Term ensures emp;
  }
{ 
  bool b = nondet_bool();
  if (b) {
    if (x>=0) {
      foo(x-1);
    }
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

dprint(simpl): ex5-nd-param-LoopNDss:17: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:or[i'::nondet{}<>&i'<=(0-1) & 0<=i
    &{FLOW,(4,5)=__norm#E}[]
; 
         i'::nondet{}<>&0<=i' & 0<=i
    &{FLOW,(4,5)=__norm#E}[]
]

Let LoopND denotes an error

  LoopND |- LoopND --> MayLoop

  LoopND |- Loop --> MayLoop

  LoopND |- * --> LoopND

  Loop |- Loop --> MayLoop

  Loop |- * --> Loop

  MayLoop |- * --> MayLoop
 
         M>N
  -----------------------------
  Term M |- Term N --> Term M

  Term M |- * --> FAIL

*/
