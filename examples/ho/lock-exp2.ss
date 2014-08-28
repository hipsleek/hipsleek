class lck extends Object {}

data cell{
  int val;
}

//Lock: initial state 
pred_prim Lock{(+)P}<x:cell>;
pred_prim Held{(-)P}<x:cell>;
pred_prim Unheld<>;

lemma_split "frac-lock-split" self::Lock{%P}(f)<x> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::Lock{%P}(f1)<x> * self::Lock{%P}(f2)<x> & 0.0<f<=1.0;

lemma "frac-lock-combine" self::Lock{%P}(f1)<x> * self::Lock{%P}(f2)<x> -> self::Lock{%P}(f1+f2)<x>;

lemma "error1" self::Held{%P}<x> * self::Unheld<> ->  emp & flow __Fail;

/******************************************/
lck create_lock(cell x) // with %P
  requires x::cell<v> & v>0
  ensures res::Lock{exists v1: x::cell<v1> & v1>0}<x>;

void acquire_lock(lck l, cell x)
  requires l::Lock{%P}(f)<x>
  ensures l::Lock{%P}(f)<x> * %P * l::Held{%P}<x>;

void release_lock(lck l, cell x)
  requires l::Held{%P}<x> * %P
  ensures emp;

void dispose_lock(lck l, cell x)
  requires l::Lock{%P}<x>
  ensures l::Unheld<> * %P;
/******************************************/

void main() requires emp ensures emp;
{
  cell a = new cell(10);
  lck l = create_lock(a);

  acquire_lock(l,a);
  assert a'::cell<v> & v>0 ; //'
  a.val = a.val +1;
  release_lock(l,a);

  acquire_lock(l,a);
  assert a'::cell<v> & v>0;//'
  a.val = a.val - 1;
  release_lock(l,a); // FAIL, since the invariant does not hold

  dispose_lock(l,a);

}
