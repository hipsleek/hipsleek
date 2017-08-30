pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}



void upd_arr(arrI base, int i, int v)
   requires base::Elem<i,_> & i>=0
   ensures base::Elem<i,v>;

void fun1(arrI base, int i, int m)
  requires base::AsegNE<i,m> 
  ensures base::AsegNE<i,m+1>;

// Should succeed

void init3(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i<m
  ensures base::AsegNE<i,m+1>;
{

  if(i<10){
    fun1(base,i,m);
  } 
}
