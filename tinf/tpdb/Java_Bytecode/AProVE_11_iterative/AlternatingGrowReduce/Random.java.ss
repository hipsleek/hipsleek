
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



data AlternatingGrowReduce
{
AlternatingGrowReduce next;
}
 void AlternatingGrowReduce_main(String[] argv)
{
  Random_args = argv;
  AlternatingGrowReduce list = AlternatingGrowReduce_createList(Random_random());
  int mode = 0;
  while (list != null) {
    if (mode == 0) {
      list = list.next.next.next.next;
    } else if (mode == 1) {
      list = new AlternatingGrowReduce(list);
    } else if (mode > 1) {
      list = new AlternatingGrowReduce(new AlternatingGrowReduce(list));
    }
    mode++;
    if (mode > 2) {
      mode = 0;
    }
  }
}

AlternatingGrowReduce AlternatingGrowReduce_createList(int length)
{
  AlternatingGrowReduce __res = new AlternatingGrowReduce(null);
  while (length > 0) {
    __res = new AlternatingGrowReduce(__res);
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