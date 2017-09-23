pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}

void upd_arr(arrI base, int i, int v)
   requires base::Elem<i,_> & i>=0
   ensures base::Elem<i,v>;


// Should fail
void init2(arrI base,int k,int m)
  requires base::AsegNE<k,m> & k>=0
  ensures base::AsegNE<k,m>;
{
  upd_arr(base,10,0);
}

