

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



data DuplicateTreePath
{

}
 void DuplicateTreePath_main(String[] args)
{
  Random_args = args;
  Tree t = Tree_createTree();
  DuplicateTreePath_duplicateRandomPath(t);
}

void DuplicateTreePath_duplicateRandomPath(Tree tree)
{
  Tree cur = tree;
  while (cur != null) {
    if (Random_random() < 42 && cur.left != null) {
      Tree t = new Tree(cur.left, cur.right);
      t.value = cur.value;
      cur.right = null;
      cur.left = t;
      cur = cur.left.left;
    } else if (cur.right != null) {
      Tree t = new Tree(cur.left, cur.right);
      t.value = cur.value;
      cur.left = null;
      cur.right = t;
      cur = cur.right.right;
    } else {
      break;
    }
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;