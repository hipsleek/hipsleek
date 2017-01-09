

data TreeLeftmostDepth
{

}
 void TreeLeftmostDepth_main(String[] args)
{
  Random_args = args;
  Tree tree = Tree_createTree();
  int lmdepth = 0;
  while (tree.left != null) {
    Tree tl = tree.left;
    Tree tll = tl.left;
    Tree tlr = tl.right;
    Tree tr = tree.right;
    tree.right = tl;
    tl.right = tr;
    tl.left = tlr;
    tree.left = tll;
    lmdepth++;
  }
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

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;