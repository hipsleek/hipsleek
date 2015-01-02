
relation dom(int[] a, int x, int y) == true.

// infer: should support array]
void initialize(ref int[] arr)
//infer [arr]
  requires dom(arr, 0, 3)
  ensures  dom(arr', 0, 3) & arr'[0]=400;
{
  arr[0] = 400;
}
               /*
void initialize1(ref int[] arr)
  infer [arr]
  requires dom(arr, 0, 3)
  ensures true;// dom(arr', 0, 3) & arr'[0]=400 &  arr'[1]=600
{
  arr[0] = 400;
  arr[1] = 600;
}

               */
