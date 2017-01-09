#include "stdhip.h"

struct GNode {
  int value;
  struct GNode *next;
  struct GNode *prev;
  struct GNode *parent;
  struct GNode *children;
};

//uncomment bellow, this bug disappears 
//struct GNode* g_node_last_child (struct GNode *node);


struct GNode*
g_node_copy (struct GNode *node)
  /*@
    requires false
  ensures true;
*/
{
  struct GNode *child;
  struct GNode* x = g_node_last_child (node);
  child = x;

  return node;
}

struct GNode*
g_node_last_child (struct GNode *node)
/*@
  requires false
  ensures true;
 */
  ;
