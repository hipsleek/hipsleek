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
void init3(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i<m & i>=0
  ensures base::AsegNE<i,m>;
{

  if(i<10 && 10<m){
    upd_arr(base,10,m);
  } 
}
