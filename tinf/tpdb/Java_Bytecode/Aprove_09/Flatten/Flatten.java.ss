

data Flatten
{

}
 void Flatten_main(String[] args)
{
  Random_args = args;
  int listLength = Random_random();
  TreeList list = null;
  
  int i = listLength;
  while (i > 0) {
    Tree tree = Tree_createTree();
    list = new TreeList(tree, list);
    i--;
  }
  
  Flatten_flatten(list);
}

ObjectList Flatten_flatten(TreeList start)
{
  ObjectList result = null;
  while (start != null) {
    Tree tree = start.value;
    if (tree != null) {
      result = new ObjectList(tree.value, result);
      start = start.next;
      start = new TreeList(tree.left, start);
      start = new TreeList(tree.right, start);
    } else {
      start = start.next;
    }
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