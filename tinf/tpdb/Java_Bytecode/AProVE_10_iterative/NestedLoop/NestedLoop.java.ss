

data NestedLoop
{

}
 void NestedLoop_main(String[] args)
{
  int i;
  int j;
  int z;
  int n;
  n = args.length;
  int[] a = new int[n];
  
  i = 0;
  while (i < n - 1) {
    a[i] = args[i]_length();
    i++;
  }
  
  
  i = 0;
  while (i < n - 1) {
    
    j = i + 1;
    while (j < n) {
      if (a[i] < a[j]) {
        z = a[i];
        a[i] = a[j];
        a[j] = z;
      }
      j++;
    }
    
    i++;
  }
  
  
  i = 0;
  while (i < n - 1) {
    i++;
  }
  
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;