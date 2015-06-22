
int randI() 
  requires Term[]
  ensures true;


void loo (ref int x, ref int y,int a, int b)
 case {
   x>0 -> 
    case {
     a=b -> requires Term[x]
       ensures true;
     a!=b -> requires MayLoop
             ensures true;
     }
   x<=0 ->
     requires Term[] ensures true;
 }
{
  int kkk=randI();
  if (x>0) {
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex20d.ss

# how to handle:

Termination checking result: 
(24)->(36) (MayTerm ERR: not bounded)[x]

 */
