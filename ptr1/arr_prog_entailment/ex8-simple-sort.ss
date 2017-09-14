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

/*
void upd_arr(arrI base, int i, int v)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;

int read_arr(arrI base, int i)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;
*/


// Should succeed

void bubble_push(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i>=0
  ensures base::AsegNE<i,m>;
{

 if(i+1<m){
     bubble_push(base,i+1,m);
     int tmp1,tmp2;
     tmp1 = read_arr(base,i);
     tmp2 = read_arr(base,i+1);
     if(tmp1>tmp2){
        upd_arr(base,i,tmp2);
	upd_arr(base,i+1,tmp1);
     }
  }
}

/*
void bubble_sort(arrI base, int i, int m)
  requires base::AsegNE<i,m> & i>=0
  ensures base::AsegNE<i,m>;
{
 if(i<m-1){
	 bubble_push(base,i,m);
	 bubble_sort(base,i+1,m);
 }
}
*/
