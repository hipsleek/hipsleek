/*
  Fine-grained locking
  Requires fractional permissions to work properly
  Was able to prove inc with split/combine
 */

data lock{}

data cell{
  lock l;
  int val;
}

lemma "splitCell" self::cell(f)<l,v> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::cell(f1)<l,v> * self::cell(f2)<l,v> & 0.0<f<=1.0;

                                                                             lemma "combineCell" self::cell(f1)<l,v> * self::cell(f2)<l,v> -> self::cell(f1+f2)<l,v>;

LOCK<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<self,v> & v>=0);

void main()
  requires true
  ensures true;
{
  lock l = new lock();
  cell x = new cell(l,0);
  init[LOCK](l,x);
  release[LOCK](l,x);

  int id;
  //dprint;
  id = fork(inc,l,x); // need a split here
  //dprint;
  acquire[LOCK](l,x);
  x.val++;
  release[LOCK](l,x);
  dprint;
  join(id);
  //dprint;

  acquire[LOCK](l,x);
  finalize[LOCK](l,x);
}

//valid
void inc(lock l,cell x)
  requires [f] l::LOCK(f)<x> & @value[l,x]
     ensures l::LOCK(f)<x>;
{
  //dprint;
  acquire[LOCK](l,x);
  //dprint;
  x.val++;
  //x.val--; //will make it fail because of the invariant
  //dprint;
  release[LOCK](l,x);
}
