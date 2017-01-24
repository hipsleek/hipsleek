class lck extends Object {}

data cell{
  int v;
}

macro L == (#,)
macro R == (,#)
macro LL == ((#,),)
macro LR == ((,#),)
macro RL == (,(#,))
macro RR == (,(,#))

//Lock: initial state
pred_prim Lock{+%P@Split}<>;
pred_prim Held{-%P@Split}<>;
pred_prim Unheld<>;

/*****************************************/
lck create_lock() // with %P
  requires emp
  ensures res::Lock{+emp}<>;

void acquire_lock(lck l)
  requires l::Lock{+%P}(f)<>
  ensures l::Lock{+%P}(f)<> * %P * l::Held{-%P}<>;

void release_lock(lck l)
  requires l::Held{-%P}<> * %P
  ensures emp;

void dispose_lock(lck l)
  requires l::Lock{+%P}<>
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
