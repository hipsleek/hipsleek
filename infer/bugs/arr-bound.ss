
int ALIM (int[] arr,  int i)
  requires  dom(arr, 0, 3) & 0<=i<=3
 ensures   res=arr[i];
{
 int k =  arr[i];
 return k;
}

int iALIM (int[] arr,  int i)
  infer[i]
  requires  dom(arr, 0, 3)// & 0<=i<=3
 ensures   res=arr[i];
{
 int k =  arr[i];
 return k;
}
