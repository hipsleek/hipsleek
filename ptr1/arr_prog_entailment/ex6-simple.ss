pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}


/*
void upd_arr(arrI base, int i, int v)
   requires base::Elem<i,_> & i>=0
   ensures base::Elem<i,v>;
*/
void fun1(arrI base, int i, int m)
  requires base::AsegNE<i,m> 
  ensures base::AsegNE<i,m+1>;




void upd_arr(arrI base, int i, int v)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;

// Should succeed

void init3(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i<m & i>=0
ensures base::AsegNE<i,m>;
{

  if(i+1<m){
    init3(base,i+1,m);
  } 
}
