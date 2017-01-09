int f(int x)
  infer [ @term
  ]
//requires true ensures true;
/*
case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> requires true ensures true;
  }
*/
case {
    x <= 0 -> requires Term ensures true;
    x > 0 & x<=8 -> requires true ensures true;
    x >10 -> requires true ensures true;
  }
{
  if (x <= 0) return 0;
  else if (x<=10) return f(x-1);
  else if (x>20) return f(x + 1);
  else if (rand_bool()) return 0;
  else return f(x);
}

/*
# mutual-5b2.ss

Problems:
 (i) why is there an @post?

Observation: 
  Verification automatically
  inserted requires false ensures false;
Problem : Please print a warning on incomplete
 case-spec and the insertion of unreachable 
 requires false ensure false.

Future Problem:
  However, if [@term,@pre] are added; we must
  use instead requires pre(..) & preT(..) ensures true & postT(..).

static  EList :EInfer @post []
          ECase case {
                 x<=0 -> EList :EBase emp&Term[32]&{FLOW,(24,25)=__norm}[]
                                        EAssume 
                                          emp&{FLOW,(24,25)=__norm}[]
                                          
                 ;
                 0<x & 
                 x<=8 -> EList :EBase emp&{FLOW,(24,25)=__norm}[]
                                        EBase emp&MayLoop[]&
                                              {FLOW,(1,27)=__flow}[]
                                                EAssume 
                                                  emp&{FLOW,(24,25)=__norm}[]
                                                  
                 ;
                 10<x -> EList :EBase emp&{FLOW,(24,25)=__norm}[]
                                        EBase emp&MayLoop[]&
                                              {FLOW,(1,27)=__flow}[]
                                                EAssume 
                                                  emp&{FLOW,(24,25)=__norm}[]
                                                  
                 ;
                 9<=x & x<=10 -> EBase hfalse&false&{FLOW,(24,25)=__norm}[] 
                 }


*/
