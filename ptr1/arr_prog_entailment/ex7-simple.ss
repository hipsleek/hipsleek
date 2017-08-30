pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}



void upd_arr(arrI base, int i, int v)
   requires base::Elem<i,_> & i>=0
   ensures base::Elem<i,v>;




/*
void upd_arr(arrI base, int i, int v)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;
*/
// Should succeed
// bachward initialization
void init3(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i<m & i>=0
  ensures base::AsegNE<i,m>;
{

  upd_arr(base,m-1,0);
  if(i+1<m){
    init3(base,i,m-1);
  } 
}
