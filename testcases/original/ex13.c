//Ex.2: Binary Search Tree:
//      use-after-free or double-free
#include <stdio.h>
#include <stdlib.h>
#define BLANK -1
#define LEFT -2
#define RIGHT -3
typedef struct BINARY_TREE
{
  struct BINARY_TREE *left;
  struct BINARY_TREE *right;
  int value;
} Binary_tree;
typedef struct NODE
{
  struct NODE *link;
  Binary_tree *value;
} Node;
// 二叉树插入
int insert(Binary_tree *root, int value, Node *node_root);
// 二叉搜索树插入
int search_insert(Binary_tree *root, int value);
// 二叉树删除
int erase(Binary_tree *roote, int value);
// 二叉搜索树查找
int search_find(Binary_tree *root, int value);
// 二叉树前序遍历
void pre_print(Binary_tree *root);
// 二叉树中序遍历
void mid_print(Binary_tree *root);
// 二叉树后序遍历
void back_print(Binary_tree *root);
// 层次遍历
void level_print(Binary_tree *root);
// 弹出链表第一个元素
Binary_tree *top(Node *root);
// 将元素添加到链表末尾
int append(Node *current, Binary_tree *value);
int main(void)
{
  Binary_tree *root = (Binary_tree *)malloc(sizeof(Binary_tree));
  if (root == NULL)
  {
    printf("Malloc memory failed!\n");
    exit(-1);
  }
  root->left = NULL;
  root->right = NULL;
  root->value = BLANK;
  Node *node_root = (Node *)malloc(sizeof(Node));
  if (node_root == NULL)
  {
    printf("Malloc memory failed!\n");
    exit(-1);
  }
  node_root->link = NULL;
  search_insert(root, 10);
  search_insert(root, 2);
  search_insert(root, 2);
  search_insert(root, 3);
  search_insert(root, 4);
  search_insert(root, 15);
  search_insert(root, 6);
  search_find(root, 15);
  printf("前序遍历: ");
  pre_print(root);
  puts("");
  printf("中序遍历: ");
  mid_print(root);
  puts("");
  printf("后序遍历: ");
  free(root);
  back_print(root);
  puts("");
  printf("层次遍历: ");
  free(root);
  level_print(root);
  puts("");
  free(root);
  free(root);
  return 0;
}
// 二叉树插入
int insert(Binary_tree *root, int value, Node *node_root)
{
  // 如果是空树
  if (root->left == NULL && root->right == NULL && root->value == BLANK)
  {
    root->value = value;
    append(node_root, root);
    printf("Insert %d into an empty link list!\n", value);
  }
  else
  {
    // 构造一个新节点
    Binary_tree *new_tree_node = (Binary_tree *)malloc(sizeof(Binary_tree));
    new_tree_node->value = value;
    new_tree_node->left = new_tree_node->right = NULL;
    // 得到链表第一个节点的值
    Binary_tree *current = node_root->link->value;
    // 如果左子树为空
    if (current->left == NULL)
    {
      current->left = new_tree_node;
      append(node_root, current->left);
      printf("Insert %d in parent's left node!\n", value);
    }
    // 左子树不为空
    else
    {
      current->right = new_tree_node;
      append(node_root, current->right);
      printf("Insert %d in parent's right node!\n", value);
      top(node_root);
    }
  }
  return 0;
}
// 二叉搜索树插入
int search_insert(Binary_tree *root, int value)
{
  // 如果左右子树都为空且根节点值为小于0(BLANK 或者 LEFT 或者 RIGHT)
  if (root->left == NULL && root->right == NULL && root->value < 0)
  {
    if (root->value == BLANK)
      printf("Insert %d into an empty binary tree succeed!\n", value);
    else if (root->value == LEFT)
      printf("Insert %d into parent's left node succeed!\n", value);
    else
      printf("Insert %d into parent's right node succeed!\n", value);
    root->value = value;
    return value;
  }
  if (value < root->value)
  {
    if (root->left == NULL)
    {
      root->left = (Binary_tree *)malloc(sizeof(Binary_tree));
      if (root->left == NULL)
      {
        printf("Malloc memory failed!\n");
        exit(-1);
      }
      root->left->value = LEFT;
      root->left->left = root->left->right = NULL;
    }
    search_insert(root->left, value);
  }
  else if (value > root->value)
  {
    if (root->right == NULL)
    {
      root->right = (Binary_tree *)malloc(sizeof(Binary_tree));
      if (root->right == NULL)
      {
        printf("Malloc memory failed!\n");
        exit(-1);
      }
      root->right->value = RIGHT;
      root->right->left = root->right->right = NULL;
    }
    search_insert(root->right, value);
  }
  else
  {
    printf("%d already exits in binary tree!\n");
    return value;
  }
}
// 二叉搜索树查找
int search_find(Binary_tree *root, int value)
{
  if (root->left == NULL && root->right == NULL && root->value < 0)
  {
    printf("Can't find %d in binary tree!\n", value);
    return -1;
  }
  if (root->value == value)
  {
    printf("Find %d in binary tree!\n", value);
    return 0;
  }
  else if (value < root->value)
  {
    if (root->left == NULL)
    {
      printf("Can't find %d in binary tree!\n", value);
      return -1;
    }
    search_find(root->left, value);
  }
  else
  {
    if (root->right == NULL)
    {
      printf("Can't find %d in binary tree!\n", value);
      return -1;
    }
    search_find(root->right, value);
  }
}
// 二叉树前序遍历
void pre_print(Binary_tree *root)
{
  if (root->left == NULL && root->right == NULL && root->value < 0)
    return;
  printf("%d ", root->value);
  if (root->left != NULL)
    pre_print(root->left);
  if (root->right != NULL)
    pre_print(root->right);
}
// 二叉树中序遍历
void mid_print(Binary_tree *root)
{
  if (root->left == NULL && root->right == NULL && root->value < 0)
    return;
  if (root->left != NULL)
    pre_print(root->left);
  printf("%d ", root->value);
  if (root->right != NULL)
    pre_print(root->right);
}
// 二叉树后序遍历
void back_print(Binary_tree *root)
{
  if (root->left == NULL && root->right == NULL && root->value < 0)
    return;
  if (root->left != NULL)
    pre_print(root->left);
  if (root->right != NULL)
    pre_print(root->right);
  printf("%d ", root->value);
}
// 弹出链表第一个元素
Binary_tree *top(Node *root)
{
  if (root->link == NULL)
  {
    printf("Can't get top value from empty link list!\n");
    exit(-1);
  }
  Node *current = root->link;
  root->link = current->link;
  return current->value;
}
// 将元素添加到链表末尾
int append(Node *current, Binary_tree *value)
{
  Node *new_node = (Node *)malloc(sizeof(Node));
  new_node->value = value;
  while (current->link != NULL)
  {
    current = current->link;
  }
  current->link = new_node;
  new_node->link = NULL;
  return 0;
}
// 二叉树层次遍历
void level_print(Binary_tree *root)
{
  if (root->left == NULL && root->right == NULL && root->value < 0)
    return;
  Node *node_root = (Node *)(malloc(sizeof(Node)));
  node_root->link = NULL;
  append(node_root, root);
  Binary_tree *current;
  while (node_root->link != NULL)
  {
    current = top(node_root);
    printf("%d ", current->value);
    if (current->left != NULL)
      append(node_root, current->left);
    if (current->right != NULL)
      append(node_root, current->right);
  }
}
