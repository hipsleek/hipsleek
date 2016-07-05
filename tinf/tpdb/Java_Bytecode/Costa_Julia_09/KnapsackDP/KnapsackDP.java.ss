
global int KnapsackDP_nbObjects;

global int[] KnapsackDP_weight = { 2, 3, 5, 2, 4, 6, 3, 1 };

global int[] KnapsackDP_utility = { 5, 8, 14, 6, 13, 17, 10, 4 };

global int KnapsackDP_weightmax = 12;

global int[][] KnapsackDP_array;
data KnapsackDP
{

}
 void KnapsackDP_consoleDisplay()
{
  int i;
  int j;
  
  i = 0;
  while (i < KnapsackDP_nbObjects) {
    
    j = 0;
    while (j <= KnapsackDP_weightmax) {
      j++;
    }
    
    i++;
  }
  
}

void KnapsackDP_Display()
{
  int i;
  int j;
  
  i = 0;
  while (i < KnapsackDP_nbObjects) {
    
    j = 0;
    while (j <= KnapsackDP_weightmax) {
      if (j != KnapsackDP_weightmax)
        {
        }
      else
        {
        }
      j++;
    }
    
    i++;
  }
  
}

void KnapsackDP_InterpretArray()
{
  int i;
  int u;
  int w;
  u = 0;
  w = KnapsackDP_weightmax;
  
  i = KnapsackDP_nbObjects - 1;
  while (i >= 1) {
    if (KnapsackDP_array[i][w] != KnapsackDP_array[i - 1][w]) {
      w = w - KnapsackDP_weight[i];
      u = u + KnapsackDP_utility[i];
    }
    i--;
  }
  
  if (KnapsackDP_array[0][w] != 0)
    ;
  {
    w = w - KnapsackDP_weight[0];
    u = u + KnapsackDP_utility[0];
  }
}

int KnapsackDP_max(int a, int b)
{
  return a > b ? a : b;
}

void KnapsackDP_SolveDP()
{
  int i;
  int j;
  KnapsackDP_array = new int[KnapsackDP_nbObjects][KnapsackDP_weightmax + 1];
  
  j = 0;
  while (j <= KnapsackDP_weightmax) {
    if (j < KnapsackDP_weight[0])
      KnapsackDP_array[0][j] = 0;
    else
      KnapsackDP_array[0][j] = KnapsackDP_utility[0];
    j++;
  }
  
  
  i = 1;
  while (i < KnapsackDP_nbObjects) {
    
    j = 0;
    while (j <= KnapsackDP_weightmax) {
      if (j - KnapsackDP_weight[i] < 0)
        KnapsackDP_array[i][j] = KnapsackDP_array[i - 1][j];
      else
        KnapsackDP_array[i][j] = KnapsackDP_max(KnapsackDP_array[i - 1][j], KnapsackDP_array[i - 1][j - KnapsackDP_weight[i]] + KnapsackDP_utility[i]);
      j++;
    }
    
    i++;
  }
  
}

void KnapsackDP_main(String[] args)
{
  KnapsackDP_nbObjects = args.length;
  KnapsackDP_SolveDP();
  KnapsackDP_Display();
  KnapsackDP_InterpretArray();
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;