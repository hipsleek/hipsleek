int foo(int x) 
 infer[@term]
  requires true
  ensures true;
/*
 case {
  x<0 -> ensures res=0;
  x>=0 -> ensures false;
}
*/
{ if (x==0) return 0;
  else 
    { if (x<0) return foo(x);
       else return foo(-x);
    };
}

/*
# mult3a.ss
 
printing problem? how come false & false
Is it hfalse & false?

Termination Inference Result:
foo:  case {
  x<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  x=0 -> requires emp & Term[31,1]
 ensures emp & true; 
  1<=x -> requires emp & Loop[]
 ensures false & false; 
  }

*/
