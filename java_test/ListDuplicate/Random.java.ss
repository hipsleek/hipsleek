
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



data ListDuplicate
{

}
 void ListDuplicate_duplicate(ObjectList list)
{
  ObjectList current = list;
  boolean even = true;
  while (current != null) {
    if (even) {
      ObjectList copy = new ObjectList(current.value, current.next);
      current.next = copy;
    }
    current = current.next;
    even = !even;
  }
}

void ListDuplicate_main(String[] args)
{
  Random_args = args;
  ObjectList list = ObjectList_createList();
  ListDuplicate_duplicate(list);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;