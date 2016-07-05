

data TreeList
{
Tree value;

TreeList next;
}
 



data Tree
{
Tree left;

Tree right;

Object value;
}
 Tree Tree_createNode()
{
  Tree result = new Tree();
  result.value = new Object();
  return result;
}

Tree Tree_createTree()
{
  int counter = Random_random();
  if (counter == 0) {
    return null;
  }
  Tree result = Tree_createNode();
  Tree t = result;
  while (counter > 0) {
    int branch = Random_random();
    if (branch > 0) {
      if (t.left == null) {
        t.left = Tree_createNode();
        t = result;
      } else {
        t = t.left;
      }
    } else {
      if (t.right == null) {
        t.right = Tree_createNode();
        t = result;
      } else {
        t = t.right;
      }
    }
    counter--;
  }
  return result;
}

void Tree_main(String[] args)
{
  Random_args = args;
  Tree_createTree();
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