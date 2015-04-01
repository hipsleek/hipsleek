

data BubbleSort
{

}
 void BubbleSort_main(String[] args)
{
  BubbleSort_sort(new int[100]);
}

void BubbleSort_sort(int[] x)
{
  int n = x.length;
  
  int pass = 1;
  while (pass < n) {
    
    int i = 0;
    while (i < n - pass) {
      if (x[i] > x[i + 1]) {
        int temp = x[i];
        x[i] = x[i + 1];
        x[i + 1] = temp;
      }
      i++;
    }
    
    pass++;
  }
  
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;