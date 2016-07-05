

data NO_04
{

}
 void NO_04_main(String[] args)
{
  
  int i = 0;
  while (i < 100) {
    int a = i + 2;
    
    int j = 0;
    while (j < a) {
      
      int k = i + j + 3;
      while (k >= 0) {
        int b = i + j + k + 4;
        
        int l = 0;
        while (l < b) {
          
          int m = i + j + k + l + 1000;
          while (m >= 0) {
            ;
            m -= 0;
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