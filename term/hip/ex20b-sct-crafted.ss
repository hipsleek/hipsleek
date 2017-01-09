
// above cannot be handled by normal size-change..

int randI() 
  requires Term[]
  ensures true;


void foo (int x, int y)
 case {
   x>0 & y>0 -> requires Term[x+y]
     ensures true;
   (x<=0 | y<=0) -> requires Term[] ensures true;
 }
{
  int kkk=randI();
  if (x>0 && y>0) {
    foo(y-2,x+1);
    dprint;
    foo(x-1,kkk);
  };
}

/*
# ex20b.ss

# why did we have two termination checking success?
# isn't there some unsoundness here?

Termination checking result: SUCCESS

!!! Inferred constraints:[ (1+pv_1193)<=pv_1192, (1+pv_1193)<=pv_1192]
Checking procedure foo$int~int... 
!!! Inferred constraints:[ 2<=pv_1192, 2<=pv_1192, pv_1192!=1, 1<=pv_1192, 1<=pv_1192]
Procedure foo$int~int SUCCESS.

Termination checking result: SUCCESS

Below not detected?

    es_var_measures 1: Some(TermErr_May[34; pv_1192]{34,pv_1192,x+y})
     es_var_stack: [ (18)->(18) (MayTerm ERR: not decreasing)  Term[34; pv_1192]
 ->  Term[34; pv_1192]]

 */
