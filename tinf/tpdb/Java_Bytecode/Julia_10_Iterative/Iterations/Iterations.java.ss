

data Iterations
{

}
 void Iterations_main(String[] args)
{
  
  int i = 0;
  while (i < args.length) {
    int a = 2 * i;
    
    int j = 0;
    while (j < a) {
      
      int k = i + j;
      while (k >= 0) {
        int b = 2 * i + 3 * j + 4 * k;
        
        int l = 0;
        while (l < b) {
          
          int m = 1000 * i + 100 * j + 10 * k + l;
          while (m >= 0) {
            ;
            m--;
          }
          
          l++;
        }
        
        k--;
      }
      
      j++;
    }
    
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