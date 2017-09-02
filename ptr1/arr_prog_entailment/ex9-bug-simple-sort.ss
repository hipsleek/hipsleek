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

int read_arr(arrI base, int i)
   requires base::Elem<i,v> & i>=0
   ensures base::Elem<i,v>;
*/
void upd_arr(arrI base, int i, int v)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;

int read_arr(arrI base, int i)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;



// Should succeed

void bubble_push(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i+1<m & i>=0
  ensures base::AsegNE<i,m>;
{

     read_arr(base,i+1);
     bool tmpb = tmpi>5;     
     upd_arr(base,i+1,0);

}
