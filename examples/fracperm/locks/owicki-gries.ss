/*
  [working example]

  Well-know Owicki-Gries example: x++ || x++

  TODO:
  (1) when we have an assertion outside the critical region,
  e.g. assert x.val=y.val+z.val, we need to incorporate the
  invariants of all locks present in the current state, i.e.
  the invariant of LOCK<x,y,z> in our example.

  (2) Not support the unifed interface for incrementor1 and
  incrementor2. Need to have the notion of ghost updates.
  For example, if we have:

  incrementor(l,x,contrib,ghost);

  Then we can write the code for main as follow

  fork incrementor(l,x,y,z); //update y, incur l::LOCK(1/2)<x,y,z>
  incrementor(l,x,y,z); // update z, incur l::LOCK(1/2)<x,z,y>

  WE CANNOT DO THIS AT THE MOMENT because there is a 
  l::LOCK(1/2)<x,y,z> in the spec of incrementor and
  the ordering of x,y,z is important (to match the actual 
  args and the formal arg of the predicate LOCK)

  This is addressed in POPL11 paper of Verifast
 */

data intCell{
  int val;
}

lemma "splitCell" self::intCell(f)<v> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::intCell(f1)<v> * self::intCell(f2)<v> & 0.0<f<=1.0;

lemma "combineCell" self::intCell(f1)<v1> * self::intCell(f2)<v> -> self::intCell(f1+f2)<v> & v1=v;

lemma "splitLock" self::LOCK(f)<x,y,z> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x,y,z> * self::LOCK(f2)<x,y,z> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<x,y,z> * self::LOCK(f2)<x,y,z> -> self::LOCK(f1+f2)<x,y,z>;


LOCK<x,y,z> == self::lock<>
  inv self!=null
  inv_lock x::intCell<x_val> * y::intCell(1/2)<y_val> * z::intCell(1/2)<z_val> & x_val=y_val+z_val;

void main()
  requires LS={}
  ensures LS'={}; //'
{
  lock l = new lock();
  intCell xCell = new intCell(0);
  intCell yCell = new intCell(0);
  intCell zCell = new intCell(0);

  //print;
  init[LOCK](l,xCell,yCell,zCell);

  release[LOCK](l,xCell,yCell,zCell);
  /* dprint; */
  int id = fork(incrementor1,l,xCell,yCell,zCell); // there is an automatic split here
  dprint;
  incrementor2(l,xCell,yCell,zCell);
  join(id);
  dprint;
}

//valid
void incrementor1(lock l,intCell x,intCell y, intCell z)
  requires l::LOCK(1/2)<x,y,z> * y::intCell(1/2)<0> & l notin LS & waitlevel<l.mu
  ensures l::LOCK(1/2)<x,y,z> * y::intCell(1/2)<1> & LS'=LS; //'
{
  acquire[LOCK](l,x,y,z);
  x.val++;
  y.val=1;
  release[LOCK](l,x,y,z);
}

//valid
void incrementor2(lock l,intCell x,intCell y, intCell z)
  requires l::LOCK(1/2)<x,y,z> * z::intCell(1/2)<0> & l notin LS & waitlevel<l.mu
  ensures l::LOCK(1/2)<x,y,z> * z::intCell(1/2)<1> & LS'=LS; //'
{
  acquire[LOCK](l,x,y,z);
  x.val++;
  z.val=1;
  release[LOCK](l,x,y,z);
}
