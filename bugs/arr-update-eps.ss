//valid
void initialize0(ref int[] arr)
  requires dom(arr, 0, 0)
  ensures  dom(arr', 0, 0) & arr'[0] = 400 ;
{
    arr[0] = 400;
   // dprint;
}

//fail
void initialize1(ref int[] arr)
               requires dom(arr, 0, 1)
               ensures  dom(arr', 0, 1) & arr'[1] = 500 & arr'[0]=400;//'
{
   arr[1] = 500;
   dprint;
   arr[0] = 400;
   dprint;
}
