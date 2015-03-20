

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



data LessLeaves
{

}
 void LessLeaves_main(String[] args)
{
  Random_args = args;
  Tree tree1 = Tree_createTree();
  Tree tree2 = Tree_createTree();
  boolean b = LessLeaves_less_leaves(tree1, tree2);
}

Tree LessLeaves_append(Tree t1, Tree t2)
{
  Tree t;
  if (t1 == null)
    return t2;
  else {
    t = t1;
    while (t.right != null) {
      t = t.right;
    }
    t.right = t2;
    return t1;
  }
}

boolean LessLeaves_less_leaves(Tree t1, Tree t2)
{
  while (t1 != null && t2 != null) {
    t1 = LessLeaves_append(t1.left, t1.right);
    t2 = LessLeaves_append(t2.left, t2.right);
  }
  if (t2 == null)
    return false;
  else
    return true;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;