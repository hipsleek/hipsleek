data cell{int val;}

//VALID
void join_dead_thread(thrd t)
  requires dead(t) ensures dead(t);
{
  /* dprint; */
  join(t);
}

//VALID
void join_thread2(thrd t)
  requires t::thrd<# emp #> or dead(t)
  ensures emp & dead(t);
{
  join(t);
  /* dprint; */
}

//VALID
void join_thread3(thrd t)
  requires t::thrd<# emp #> or dead(t)
  ensures emp & dead(t);
{
  join(t);
  /* dprint; */
}

//FAIL with --classic, VALID
void test(thrd t)
  requires t::thrd<# emp #>
  ensures t!=null;
{
  ;
}


//VALID
bool must_dead(thrd t)
 case{
  t!=null -> ensures !res;
  t=null -> requires dead(t) ensures res;}

//VALID
bool check_must_dead(thrd t)
  requires t::thrd<# emp #>
  ensures !res;
{
  bool b = must_dead(t);
  if (!b){
    join(t);
  }
  return b;
}

//helper
//deliberately introduce dead(t1)
void introduce_dead(thrd t1)
  requires true
  ensures dead(t1);

//FAIL
void check_liveness(thrd t1, cell x)
  requires t1::thrd<# x::cell<_> & true #>
  ensures false;
{
  introduce_dead(t1); //FAIL, t-inconsistency detected
  dprint;
}

//helper
//deliberately introduce a thread node
void introduce_thread(thrd t1,cell x)
  requires true
  ensures t1::thrd<# x::cell<_> & true #>;

//FAIL
void check_liveness2(thrd t1)
  requires dead(t1)
  ensures false;
{
  cell x;
  introduce_thread(t1,x); //FAIL, t-inconsistency detected
  dprint;
}
