class rExp extends __Exc {
   int val;
}

int foo(int N) 
 requires N>=0
 ensures res=N;
{
 int i = 0;
 try {
  loop(i,N);
 } catch (rExp ot) {
   return ot.val;
 };
}

void loop(ref int i, int N)
  requires i<=N
  ensures eres::rExp<ot> & i'=N & ot=i' & flow rExp;
 {
    if (i>=N) {
        raise new rExp(i);
    }
    i = i+1;
    loop(i,N);
}


/*
todo:
- modify astsimp.while_return
  - add rExp (done)
  - raise exp ()
-modify trans_exp:WHILE: specs
- modify body of foo
-
 */
