
global int[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
	dom(Random_args,1,10);
  int string = Random_args[Random_index];
  Random_index++;
  return 1;
}

