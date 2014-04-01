/*
  A variant of the motivating example in Fig.1
  where resource is split using fractional permissions.
 */

//memory cell
data cell{ int val;}

//fractional permission split for cell
lemma "splitCell" self::cell(f)<v> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::cell(f1)<v> * self::cell(f2)<v> & 0.0<f<=1.0;

////fractional permission combine for cell
lemma "combineCell" self::cell(f1)<v> * self::cell(f2)<v> -> self::cell(f1+f2)<v>;

/* // */

//deallocate a cell
void destroyCell(cell a)
  requires a::cell<_>
  ensures true;

void thread1(cell x, cell y)
  requires x::cell<0> * y::cell<0>
  ensures x::cell<1> * y::cell<2>;
{
  x.val = x.val + 1;
  y.val = y.val + 2;
}

void thread2(thrd t1, cell x, cell y)
  requires t1::thrd<# x::cell(0.6)<1> * y::cell(0.6)<2> & true #>
  ensures x::cell(0.6)<1> * y::cell(0.6)<2>;
{
  join(t1);
  int a = x.val + y.val;
  assert a'=3; //'
}

void main()
  requires true ensures true;
{

  cell x = new cell(0);
  cell y = new cell(0);

  thrd t1 = fork(thread1,x,y);
  thrd t2 = fork(thread2,t1,x,y); //fractional split of resource required

  join(t1);
  int a = x.val + y.val;
  assert a'=3; //'

  join(t2);

  assert x'::cell<1> * y'::cell<2>;

  destroyCell(x);
  destroyCell(y);
}
