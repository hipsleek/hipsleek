/*
  Fine-grained locking
  Requires fractional permissions to work properly
  Was able to prove inc with split/combine

  ISSUES: worst performace because of so many splits
 */

data lock{}

data cell{
  lock l;
  int val;
}

/* lemma "splitCell" self::cell(f)<l,v> & f=f1+f2 -> self::cell(f1)<l,v> * self::cell(f2)<l,v> & 0.0<f<=1.0; */
//lemma "splitCell" self::cell(f)<l,v> & f=f1+f2 -> self::cell(f1)<l,v>@D * self::cell(f2)<l,v>@D;

//lemma "combineCell" self::cell(f1)<l,v> * self::cell(f2)<l,v> -> self::cell(f1+f2)<l,v>;

/* lemma "splitLOCK" self::LOCK(f)<v> & f=f1+f2 -> self::LOCK(f1)<v> * self::LOCK(f2)<v> & 0.0<f<=1.0; */
lemma "splitLOCK" self::LOCK(f)<v> & f=f1+f2 -> self::LOCK(f1)<v>@D * self::LOCK(f2)<v>@D;

lemma "combineLOCK" self::LOCK(f1)<v> * self::LOCK(f2)<l> -> self::LOCK(f1+f2)<l>;

LOCK<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<self,v> & v>=0);

void main()
  requires true
  ensures true;
{
  lock l = new lock();
  cell x = new cell(l,0);
  dprint;
  init[LOCK](l,x);
  dprint;
  release[LOCK](l,x);
  int id;
  dprint;
  //id = fork(inc,l,x); // need a split here
  dprint;
  acquire[LOCK](l,x);
  dprint;
  //x.val++;
  dprint;
  release[LOCK](l,x);
  dprint;
  //join(id);
  //dprint;
  acquire[LOCK](l,x);
  dprint;
  finalize[LOCK](l,x);
  dprint;
}

//valid
void inc(lock l,cell x)
  requires [f] l::LOCK(f)<x> & @value[l,x]
     ensures l::LOCK(f)<x>;
{
  //dprint;
  acquire[LOCK](l,x);
  //dprint;
  x.val++; //so many split here, need to control when to split
  //x.val--; //will make it fail because of the invariant
  //dprint;
  release[LOCK](l,x);
}
