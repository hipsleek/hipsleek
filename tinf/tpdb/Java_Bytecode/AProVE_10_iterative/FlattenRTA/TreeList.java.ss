

data TreeList
{
Tree value;

TreeList next;
}
 



data Tree
{
Tree left;

Tree right;

int value;
}
 Tree Tree_createNode()
{
  Tree result = new Tree();
  result.value = Random_random();
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



data IntList
{
int value;

IntList next;
}
 IntList IntList_createList()
{
  IntList result = null;
  int length = Random_random();
  while (length > 0) {
    result = new IntList(Random_random(), result);
    length--;
  }
  return result;
}



data FlattenRTA
{

}
 IntList FlattenRTA_flatten(TreeList list)
{
  TreeList cur = list;
  IntList result = null;
  while (cur != null) {
    Tree tree = cur.value;
    if (tree != null) {
      IntList oldIntList = result;
      result = new IntList();
      result.value = tree.value;
      result.next = oldIntList;
      TreeList oldCur = cur;
      cur = new TreeList();
      cur.value = tree.left;
      cur.next = oldCur;
      oldCur.value = tree.right;
    } else
      cur = cur.next;
  }
  if (cur != list)
    {
    }
  return result;
}

void FlattenRTA_main(String[] args)
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
  
  FlattenRTA_flatten(list);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;