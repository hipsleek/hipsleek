int Ack(int m, int n)
  infer[@term]
  requires true
  ensures res>=n+1;
{
  if (m == 0) return n + 1;
  else if (n == 0) return Ack(m-1, 1);
  else return Ack(m-1, Ack(m, n-1));
}

/*
#i-ex8-ack-ack.ss --dis-term-add-post

This works with res>=n+1
but not f91 which seems to require a more precise post.


                      ((m=3 & n=0) | (2<=m & 
                      1<=n)) -> requires emp & MayLoop[]
     ensures true & true;
                      
                      n=0 & 
                      m=4 -> requires emp & MayLoop[]
     ensures true & true;
                      
                      n=0 & 
                      5<=m -> case {
                               n=0 & 
                               m=5 -> requires emp & MayLoop[]
     ensures true & true;
                               
                               6<=m -> case {
                                        (m<=6 | (n=0 & 
                                        7<=m)) -> requires emp & MayLoop[]
     ensures true & true;
                                        
                                        }
                               
                               }
                      
*/
