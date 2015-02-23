/*
  A variant of the motivating example in Fig.1
  where resource is split using fractional permissions.
 */

//memory cell

pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

void thread1(ref int x, ref int y)
     requires @full[x,y] 
     ensures @full[x,y] & x'=x+1 & y'=y+2;
{
  x = x + 1;
  y = y + 2;
}

Thrd fork_thread1(ref int x, ref int y)
  requires @full[x,y] 
  ensures res::Thrd{+@full[x,y] & x'=x+1 & y'=y+2}<>;

void thread2(Thrd t1, ref int x, ref int y)
  requires t1::Thrd{+ @frac(1/2)[x,y]}<> * @value[t1]
  ensures  @frac(1/2)[x,y] & x'=x & y'=y;
{
  join2(t1);
  dprint;
  int a = x + y;
  assert a'=3; //'
}

Thrd fork_thread2(Thrd t1, ref int x, ref int y)
  requires t1::Thrd{+ @frac(1/2)[x,y]}<> * @value[t1]
  ensures  res::Thrd{+ @frac(1/2)[x,y] & x'=x & y'=y}<>;

void main()
  requires true ensures true;
{

  int x = 0;
  int y = 0;

   Thrd t1 = fork_thread1(x,y);
  dprint;
  Thrd t2;
  t2 = fork_thread2(
  t1,
  x,
  y); //fractional split of resource required

  /*

#ex41.ss

id: 7; caller: []; line: 51; classic: false; kind: Check_Specs; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp

checkentail (htrue) * 
  t1_40'::Thrd{ + emp*N@full[x_38,y_39]
     &x_38'=1+x_38 & y_39'=2+y_39&{FLOW,(4,5)=__norm#E}[]}<>
* N@full[t1_40,t2_41]@zero[x_38,y_39]&{FLOW,(4,5)=__norm#E}[]
 |-  emp*N@full[x_38,y_39]@lend[t1_40]&{FLOW,(4,5)=__norm#E}[]. 

Thrd fork_thread2(Thrd t1, ref int x, ref int y)
  requires t1::Thrd{+ @frac(1/2)[x,y]}<> * @value[t1]
  ensures  res::Thrd{+ @frac(1/2)[x,y] & x'=x & y'=y}<>;

What happen to frac? Why did we have 
                                full[x,y]@lend[t]?

What is check_specs?


*/

  join2(t1);
  int a = x + y;
  assert a'=3; //'

  join2(t2);

  assert x'=1 & y'=2;

}
