

data RunningPointers
{

}
 boolean RunningPointers_isCyclic(ObjectList l)
{
  if (l == null) {
    return false;
  }
  ObjectList l1;
  ObjectList l2;
  l1 = l;
  l2 = l.next;
  while (l2 != null && l1 != l2) {
    l2 = l2.next;
    if (l2 == null) {
      return false;
    } else if (l2 == l1) {
      return true;
    } else {
      l2 = l2.next;
    }
    l1 = l1.next;
  }
  return l2 != null;
}

void RunningPointers_main(String[] args)
{
  Random_args = args;
  ObjectList list = ObjectList_createList();
  RunningPointers_isCyclic(list);
}


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



data ObjectList
{
Object value;

ObjectList next;
}
 ObjectList ObjectList_createList()
{
  ObjectList result = null;
  int length = Random_random();
  while (length > 0) {
    result = new ObjectList(new Object(), result);
    length--;
  }
  return result;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;