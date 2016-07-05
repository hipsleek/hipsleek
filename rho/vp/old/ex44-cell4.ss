/*
  [working example]
  Fine-grained locking
  Requires fractional permissions to work properly
  Was able to prove inc with automatic split/combine
  NOTE: split/combine lemmas can be generated dynamically
  based on certain templates

  Output:
Procedure inc$lock~cell SUCCESS
Procedure main$ SUCCESS

 */

data cell{
  lock l;
  int val;
}

//lemma "splitCell" self::cell(f)<l,v> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::cell(f1)<l,v> * self::cell(f2)<l,v> & 0.0<f<=1.0;

//lemma "combineCell" self::cell(f1)<l,v> * self::cell(f2)<l,v> -> self::cell(f1+f2)<l,v>;

lemma "splitLock" self::LOCK(f)<x> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x> * self::LOCK(f2)<x> & 0.0<f<=1.0;

                                                                  lemma "combineLock" self::LOCK(f1)<x> * self::LOCK(f2)<x> -> self::LOCK(f1+f2)<x>;


LOCK<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<self,v> & v>=2);

void main()
  requires LS={}
  ensures LS'={}; //'
{
  lock l = new lock();
  cell x = new cell(l,2);
  //print;
  init[LOCK](l,x);

  release(l);

  thrd id;
  id = fork(inc,l,x); // there is an automatic split here

  acquire(l);
  x.val++;
  release(l);

  join(id);

  acquire(l);

  finalize(l);

}

//valid
void inc(lock l,cell x)
  requires [f] l::LOCK(f)<x> & @value[l,x] & l notin LS & waitlevel<l.mu
  ensures l::LOCK(f)<x> & LS'=LS; //'
{
  dprint;
  acquire(l);
  x.val--;
  x.val++;
  //x.val--; //will make it fail because of the invariant
  release(l);
}
