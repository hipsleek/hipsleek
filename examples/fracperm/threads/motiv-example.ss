//memory cell
data cell{ int val;}

//permission split for cell
lemma "splitCell" self::cell(f)<v> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::cell(f1)<v> * self::cell(f2)<v> & 0.0<f<=1.0;

//permission combine for cell
lemma "combineCell" self::cell(f1)<v> * self::cell(f2)<v> -> self::cell(f1+f2)<v>;

//

void thread1(cell x, cell y)
  requires x::cell<0> * y::cell<0>
  ensures x::cell<1> * y::cell<2>;
{
  x.val = x.val + 1;
  y.val = y.val + 2;
}

void main()
  requires true ensures true;
{

  cell x = new cell(0);
  cell y = new cell(0);
  thrd id = fork(thread1,x,y);
  dprint;
  int id1;
  join(id1);
  assert x'::cell<1> * y'::cell<2>;
}
