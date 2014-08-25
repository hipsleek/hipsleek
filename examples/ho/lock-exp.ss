class lck extends Object {}

data cell{
  int v;
}

//Lock: initial state 
pred_prim Lock{(+)P}<>;
pred_prim Held{(-)P}<>;
pred_prim Unheld<>;

lemma_split "frac-lock-split" self::Lock{%P}(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::Lock{%P}(f1)<> * self::Lock{%P}(f2)<> & 0.0<f<=1.0;

lemma "frac-lock-combine" self::Lock{%P}(f1)<> * self::Lock{%P}(f2)<> -> self::Lock{%P}(f1+f2)<>;

lemma "error1" self::Held{%P}<> * self::Unheld<> ->  emp & flow __Fail;

/*****************************************/
lck create_lock() // with %P
  requires emp
  ensures res::Lock{emp}<>;

void acquire_lock(lck l)
  requires l::Lock{%P}(f)<>
  ensures l::Lock{%P}(f)<> * %P * l::Held{%P}<>;

void release_lock(lck l)
  requires l::Held{%P}<> * %P
  ensures emp;

void dispose_lock(lck l)
  requires l::Lock{%P}<>
  ensures l::Unheld<> * %P;
/*****************************************/

void main() requires emp ensures emp;
{
  lck x = create_lock();

  acquire_lock(x);
  release_lock(x);

  acquire_lock(x);
  release_lock(x);

  dispose_lock(x);

}
