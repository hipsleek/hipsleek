data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [Q]
  requires c::cell<v>@L
  ensures c::cell<w>@b & Q(b)  ;
{
 int x = c.fst;
 if (x!=1) {
   //c.fst =c.fst-1;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}

/*
# ex8e1e.ss --trace-exc

int foo(cell c)
  infer [Q]
  requires c::cell<v>@L
  ensures c::cell<w>@b & Q(b)  ;

# @L exception failure.

ERROR: at _0:0_0:0
Message: compute_def:Error in translating the input for fixcalc
Exception(compute_def):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint_aux):Failure("compute_def:Error in translating the input for fixcalc")
Exception(compute_fixpoint):Failure("compute_def:Error in translating the input for fixcalc")



*/
