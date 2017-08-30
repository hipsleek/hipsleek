pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}


void upd_arr(arrI base, int i, int v)
   requires base::Elem<i,_> & i>=0
   ensures base::Elem<i,v>;

void init1(arrI base,int i,int m)
  requires base::AsegNE<i,m> 
  ensures base::AsegNE<i,m>;
{
    upd_arr(base,i,0);
}
