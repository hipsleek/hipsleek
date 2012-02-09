// infer: should support array
void initialize(ref int[] arr)
  infer [arr]
  requires dom(arr, 0, 0)
  ensures true;// dom(arr', 0, 0) & arr'[0]=400
{
  arr[0] = 400;
}

void initialize1(ref int[] arr)
  infer [arr]
  requires dom(arr, 0, 3)
  ensures true;// dom(arr', 0, 3) & arr'[0]=400 &  arr'[1]=600
{
  arr[0] = 400;
  arr[1] = 600;
}

