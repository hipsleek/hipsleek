pred_prim Aseg<start:int, end:int>;
pred_prim AsegNE<start:int, end:int>;
pred_prim Elem<start:int,value:int>;

data arrI {
  int val;
}


int read_ptr(arrI ptr)
   requires base::Elem<i,v> & ptr = base + i
   ensures base::Elem<i,v> & res = v;

void upd_arr(arrI ptr, int v)
   requires base::Elem<i,_> & ptr = base + i
   ensures base::Elem<i,v>;

arrI ptr_add(arrI ptr, int index)
   requires ptr!=null
   ensures res = ptr + index;

arrI alloc(int length)
   requires emp & length>0
   ensures res::AsegNE<0, length>  & res!=null;

int main(){
      arrI ptr = alloc(10);
      
      int index = 0;
      while(index<10)
	requires b1::Elem<i, v> & ptr = b1+i // if write it as ptr::Elem<i,v>, ptr has to be the base
	ensures b1::Elem<i, v>;
	{
            read_ptr(ptr);
	    index = index + 1;
	}
      return 0;
}

