data ring {
    int[] arr; // buffer contents
    int size; // buffer capacity
    int fst;  // queue head
    int length; // queue length (maybe 0)
}

// list property not yet captured
buf<s,f,l> == self::ring<arr,s,f,l> 
  & dom(arr,0,s-1)  // array allocated from 0 to s or s-1?
  & 0<=l<=s & s>0 & 0<=f<s
inv s>=1 & 0<=l<=s;

ring create(int n)
  requires n>0
  ensures res::buf<n,0,0>;
{
  int[] a = new int[n];
  return new ring(a,n,0,0);
}

ring create1(int n)
  requires n>0
  ensures res::buf<n,0,0>;
{
  return new ring(new int[n],n,0,0);
}
