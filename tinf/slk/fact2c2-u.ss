UTPre@fact fpre(int x).
UTPost@fact fpost(int x).

int fact(int x)
  infer [@term]
/*
  requires fpre(x) 
  ensures res>=1 & fpost(x);
*/
  case {
    x = 0 -> requires Term ensures res>=1;
    x != 0 -> requires true ensures res>=1;
  }
{
  if (x==0) return 1;
  else {
    return 1 + fact(x - 1);
  }
}

/*
# fact2c2-u.ss

This generated a requires hfalse ensures hfalse.

 case {
  x=0 -> requires emp&Term[29]
 ensures emp&1<=res; 
  x!=0 -> case {
           1<=x -> requires emp&Term[29,3,-1+(1*x)]
 ensures emp&1<=res; 
           x<=(0-1) -> requires emp&Loop[]
 ensures hfalse&false; 
           x=0 -> requires hfalse&false
 ensures hfalse&false; 
           }
  
  }

Maybe we can flatten the two cases into a single one,
as a further simplification step, to give:

 case {
  x=0 -> requires emp&Term[29]
 ensures emp&1<=res; 
           1<=x -> requires emp&Term[29,3,-1+(1*x)]
 ensures emp&1<=res; 
           x<=(0-1) -> requires emp&Loop[]
 ensures hfalse&false; 
 }

You should implement this as another transformation
step on case-spec.
*/
