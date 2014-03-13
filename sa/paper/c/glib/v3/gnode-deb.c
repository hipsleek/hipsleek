#include "stdhipmem.h"

struct GNode {
  int value;
  struct GNode *next;
  struct GNode *prev;
  struct GNode *parent;
  struct GNode *children;
};


struct GNode*
g_node_new (int value)
/*@
  requires true
  ensures res::GNode<value,null,null,null,null>;
*/
{
  struct GNode *node = malloc(sizeof(struct GNode));

  node->value = value;
  node->next = NULL;
  node->prev = NULL;
  node->parent = NULL;
  node->children = NULL;

  return node;
}

/*@
HeapPred H_copy(GNode a).
HeapPred G_copy(GNode a).
*/

struct GNode*
g_node_copy (struct GNode *node)
/*@
  infer [H_copy, G_copy]
  requires H_copy(node)
  ensures G_copy(res);
*/
{
  struct GNode *new_node = NULL;

  if (node)
    {
      struct GNode *child;

      new_node = g_node_new (node->value);
      struct GNode* x = g_node_last_child (node);
      for (child = x; child; child = child->prev)
	g_node_prepend (new_node, g_node_copy (child));
    }

  return new_node;
}



/*@
HeapPred H_lch(GNode a).
HeapPred G_lch(GNode a, GNode b).
*/

struct GNode*
g_node_last_child (struct GNode *node)
{
  if (node == NULL)
    {
      return NULL;
    }

  node = node->children;
  if (node)
    {
    while (node->next)
      /*@
        infer [H_lch, G_lch]
        requires H_lch(node)
        ensures G_lch(node, node');
      */
      {
        node = node->next;
      }
    }

  return node;
}


/*@
HeapPred H1_prep(GNode a).
HeapPred H2_prep(GNode a).
HeapPred G_prep(GNode a).
*/

struct GNode*
g_node_prepend (struct GNode *parent,
		struct GNode *node)
/*@
  infer [H1_prep, H2_prep, G_prep]
  requires H1_prep(parent) * H2_prep(node)
  ensures G_prep(res);
*/
{
  if (parent == NULL) return node;
  
  return g_node_insert_before (parent, parent->children, node);
}

/*@
HeapPred H_insb(GNode a).
HeapPred G_insb(GNode a, GNode b).
HeapPred H_insb1(GNode a,GNode b, GNode c).
HeapPred G_insb1(GNode a, GNode b,  GNode c).
*/

//???
struct GNode*
g_node_insert_before (struct GNode *parent,
		      struct GNode *sibling,
		      struct GNode *node)
/*@
  infer [H_insb1, G_insb1]
  requires H_insb1(parent, sibling, node)
  ensures G_insb1(parent, sibling, node);
*/
{
  if (parent == NULL)
    {
      return node;
    }

  if (node == NULL)
    {
      return node;
    }

  if (node->parent != NULL ||
      node->prev != NULL ||
      node->next != NULL)
    {
      return node;
    }

  if (sibling && sibling->parent != parent)
    {
      return node;
    }

  node->parent = parent;

  if (sibling)
    {
      if (sibling->prev)
	{
	  node->prev = sibling->prev;
	  node->prev->next = node;
	  node->next = sibling;
	  sibling->prev = node;
	}
      else
	{
	  node->parent->children = node;
	  node->next = sibling;
	  sibling->prev = node;
	}
    }
  else
    {
      if (parent->children)
	{
	  sibling = parent->children;
	  while (sibling->next)
            /*@
              infer [H_insb, G_insb]
              requires H_insb(sibling)
              ensures G_insb(sibling, sibling');
            */
            {
	      sibling = sibling->next;
            }
          //  sibling'::GNode<_,_,_,_,_> * node'::GNode<_,_,_,_,_> ;
	  node->prev = sibling;
	  sibling->next = node;
	}
      else
	node->parent->children = node;
    }

  return node;
}

/*@
HeapPred H_copd(GNode a).
HeapPred G_copd(GNode a, GNode b).
*/

struct GNode*
g_node_copy_deep (struct GNode *node, 
		  int copy_func,
		  int val)
{
  struct GNode *new_node = NULL;

  if (!copy_func)
    return g_node_copy (node);

  if (node)
    {
      struct GNode *child, *new_child;

      new_node = g_node_new (val);
      struct GNode * tmp = g_node_last_child (node);
      for (child = tmp; child; child = child->prev)
        /*@
          infer [H_copd, G_copd]
          requires H_copd(child)
          ensures G_copd(child, child');
        */
	{
	  new_child = g_node_copy_deep (child, copy_func, val);
	  g_node_prepend (new_node, new_child);
	}
    }

  return new_node;
}
