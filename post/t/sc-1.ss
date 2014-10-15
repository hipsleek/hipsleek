/* Example suggested by Shengchao */

void f(int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else f(x + y, x + y);
}

/*
# sc-1.ss

Long : Can we improve the presentation of case-spec to use
the following indentation by controlling pr proc
in cprinter.ml

Termination Inference Result:
f:case { 0<=x 
  -> case { 0<=y 
     -> requires emp & Loop[]
        ensures false & false; 
           y<=(0-1) 
     -> case { x<=0 
        -> requires emp & Term[29,5]
           ensures emp & true; 
               1<=x 
        -> case {(0-x)<=y & y<=(0-1) 
           -> requires emp & Loop[]
              ensures false & false;
                 1<=x & x<=((0-y)-1) 
           -> requires emp & Term[29,10]
              ensures emp & true;
           }
        }
     }
          x<=(0-1) 
   -> requires emp & Term[29,1]
      ensures emp & true; 
  }
*/
