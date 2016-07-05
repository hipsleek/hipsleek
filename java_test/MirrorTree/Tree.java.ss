

data Tree
{
Tree left;

Tree right;

Object value;
}
 Tree Tree_createNode()
{
  if (Random_random() == 0) {
    return null;
  }
  Tree result = new Tree();
  return result;
}

Tree Tree_createTree()
{
  Tree result = Tree_createNode();
  List list = new List(result, null);
  int counter = Random_random();
  while (counter > 0 && list != null) {
    Tree first = list.value;
    list = list.next;
    if (first != null) {
      Tree left = Tree_createNode();
      Tree right = Tree_createNode();
      first.left = left;
      first.right = right;
      list = new List(left, list);
      list = new List(right, list);
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



data MirrorTree
{

}
 void MirrorTree_main(String[] args)
{
  Random_args = args;
  Tree tree = Tree_createTree();
  MirrorTree_mirror(tree);
}

void MirrorTree_mirror(Tree tree)
{
  Tree cur = tree;
  while (cur != null) {
    Tree t = cur.left;
    cur.left = cur.right;
    cur.right = t;
    cur = cur.right;
  }
}



data List
{
Tree value;

List next;
}
 

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;