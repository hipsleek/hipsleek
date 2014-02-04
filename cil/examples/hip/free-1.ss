data int__star {
 int pdata;
}

pred_prim memLoc<heap:bool,size:int>
  inv size>0;

int__star heap_alloc_int_star(int n) 
  requires n>0
  ensures res::int__star<_> * res::memLoc<h,n> & h;

int__star stack_alloc_int_star(int n) 
  requires n>0
  ensures res::int__star<_> * res::memLoc<h,n> & !h;


void free_heap(int__star p)
 requires p::int__star<n> * p::memLoc<h,_> & h // FAIL here, in "true"
//requires p::memLoc<h,_> & h // FAIL here, in "true"
 ensures emp;



void foo ()
{
  int__star p = heap_alloc_int_star(1);
  dprint;
  p.pdata = 1;
  //int i = 2;
  dprint;
  free_heap(p);
  dprint;
}
