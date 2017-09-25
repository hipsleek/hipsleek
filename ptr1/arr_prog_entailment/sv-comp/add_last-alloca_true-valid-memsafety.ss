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
   
/*
arrI ptr_inc(arrI ptr)
   requires true
   ensures res = ptr+1;
*/


arrI ptr_add(arrI ptr, int index)
   requires ptr!=null
   ensures res = ptr + index;



arrI alloc(int length)
   requires emp & length>0
   ensures base::AsegNE<0, length> & res = base & base!=null;

int main(){
	   arrI ptr = alloc(10);

	   arrI tmp_ptr = ptr_add(ptr, 50);
	   // tmp_ptr = ptr_add(tmp_ptr, 5);

	   read_ptr(tmp_ptr);
	   return 0;
}

/*
base::AsegNE<0, length-1> & ptr = base & tmp_ptr = ptr |- exists base', i: base'::Elem<i, v> & tmp_ptr = base' + i & base' = base

if can do this:

base::AsegNE<0, length-1> & ptr = base & tmp_ptr = ptr |- exists i: base::Elem<i, v> & tmp_ptr = ptr + i.
*/
