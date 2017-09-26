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
   requires emp & true
   ensures res = ptr + index;

arrI alloc(int length)
   requires emp & length>0
   ensures res::AsegNE<0, length>  & res!=null;

int main(){
      arrI ptr = alloc(10);
		
      int index = 0;
      arrI a = ptr;
      arrI end = ptr_add(ptr, 9);
      

      while( read_ptr( a )!= 0 )
        requires ptr::AsegNE<k, 10> & a=ptr+k & k>=0 & k<=9 & end = ptr+9
        ensures ptr::AsegNE<k, 10>;
      {
	upd_arr(a, read_ptr(end));
	a = ptr_add(a, 1);
	    
      }
      return 0;
}

/*
fun(int[] arr, int index, int length)
   arr::Aseg<index, length>
{
   if (arr[index] == arr[length-1])
      return;
   else
      fun(arr, index+1, length)
}
   
*/
