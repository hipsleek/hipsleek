int mc91(int n)
infer[@term] 
//requires true ensures res>=91;
requires true ensures n>=101 & res=n-10 | n<101 & res=91;
/*
infer[@term] requires true ensures res>=91;
 case {
   n>=101 -> requires Term[] 
     ensures //(res>=91 & n<=100 | n=res+1) & 
     res>=91;
   n<101 -> requires Term[100-n] ensures res >=91;
 }
*/
{
  if (n > 100) return n-10;
  else return mc91(mc91(n+11));
}

/*
# i-ex9-f91-rec.ss --dis-term-add-post

It seems that res>=91 is not sufficient.

Termination Inference Result:
mc91:  requires true & truecase {
                      101<=n -> requires emp & Term[69,1]
     ensures emp & 91<=res;
                      
                      n<=100 -> requires emp & MayLoop[]
     ensures emp & 91<=res;
                      
                      }

*/
