pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}



void upd_arr(arrI base, int i, int v)
   requires base::Elem<i,_> & i>=0
   ensures base::Elem<i,v>;


int read_arr(arrI base, int i)
   requires base::Elem<i,v> & i>=0
   ensures base::Elem<i,v> & res=v;

/*
void upd_arr(arrI base, int i, int v)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;

int read_arr(arrI base, int i)
   requires base::AsegNE<i,i+1> & i>=0
   ensures base::AsegNE<i,i+1>;
*/


// Should succeed

int selectMax(arrI base,int i,int m)
  requires base::AsegNE<i,m> & i>=0
  ensures base::AsegNE<i,m>;
{

 if(i+1<m){
    int tmpv = select(base,i+1,m);
	int tmp1;
	tmp1 = read_arr(base,i);
	if(tmp1<tmpv){
	   return tmpv;
        }
	else{
	   return tmp1;
       }
     }
   else{
	return read_arr(base,i);
   }
}
