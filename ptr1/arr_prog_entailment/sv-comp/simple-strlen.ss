int read_ptr(arrI ptr)
   requires base::Elem<i,v> & ptr = base + i
   ensures base::Elem<i,v> & res = v;

void upd_arr(arrI ptr, int v)
   requires base::Elem<i,_> & ptr = base + i
   ensures base::Elem<i,v>;

arrI ptr_add(arrI ptr, int index)
   requires emp 
   ensures res = ptr + index;

arrI alloc(int length)
   requires emp & length>0
   ensures base::AsegNE<0, length> & res = base & base!=null;

int str_length(arrI ptr)
  requires base::Aseg<i, k> * base::Elem<k,-100> & ptr = base+i
  ensures base::Aseg<i, k+1>;
{
  if(read_ptr(ptr)== -100){
    assume false;
    return 0;
  }
  else{
    int tmp_l = str_length(ptr_add(ptr, 1));
    return tmp_l + 1;
  }
}


