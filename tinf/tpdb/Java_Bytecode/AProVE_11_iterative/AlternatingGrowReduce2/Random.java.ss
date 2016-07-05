
global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}



data AlternatingGrowReduce2
{
AlternatingGrowReduce2 next;
}
 void AlternatingGrowReduce2_main(String[] argv)
{
  Random_args = argv;
  AlternatingGrowReduce2 list = AlternatingGrowReduce2_createList(Random_random());
  int mode = 0;
  while (list != null) {
    if (mode == 0) {
      list = list.next;
    } else if (mode == 1) {
      list = new AlternatingGrowReduce2(list);
    } else if (mode > 1) {
      list = list.next;
    }
    mode++;
    if (mode > 2) {
      mode = 0;
    }
  }
}

AlternatingGrowReduce2 AlternatingGrowReduce2_createList(int length)
{
  AlternatingGrowReduce2 __res = new AlternatingGrowReduce2(null);
  while (length > 0) {
    __res = new AlternatingGrowReduce2(__res);
    length--;
  }
  return __res;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;