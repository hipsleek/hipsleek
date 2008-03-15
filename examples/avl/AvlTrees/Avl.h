// <plaintext>
#ifndef AVL_H
#define AVL_H

#include <stddef.h>
#include "Comparable.h"

class  ostream;

// Indices into a subtree array
//     NOTE: I would place this inside the AvlNode class but 
//           when I do, g++ complains when I use dir_t. Even
//           when I prefix it with AvlNode:: or AvlNode<KeyType>::
//           (If you can get this working please let me know)
//
enum  dir_t { LEFT = 0, RIGHT = 1 };

// AvlNode -- Class to implement an AVL Tree
//
template <class KeyType>
class AvlNode {
public:
      // Max number of subtrees per node
   enum  { MAX_SUBTREES = 2 };

      // Return the opposite direction of the given index
   static  dir_t
   Opposite(dir_t dir) { 
     return dir_t(1 - int(dir));
   }

   // ----- Constructors and destructors: 

   AvlNode(Comparable<KeyType>  * item=NULL);
   virtual ~AvlNode(void);

   // ----- Query attributes:

      // Get this node's data
   Comparable<KeyType> *
   Data() const { return  myData; }

      // Get this node's key field
   KeyType
   Key() const { return  myData->Key(); }

      // Query the balance factor, it will be a value between -1 .. 1
      // where:
      //     -1 => left subtree is taller than right subtree
      //      0 => left and right subtree are equal in height
      //      1 => right subtree is taller than left subtree
   short
   Bal(void) const { return  myBal; }

      // Get the item at the top of the left/right subtree of this
      // item (the result may be NULL if there is no such item).
      //
   AvlNode *
   Subtree(dir_t dir) const { return  mySubtree[dir]; }

   // ----- Search/Insert/Delete
   //
   //   NOTE: These are all static functions instead of member functions
   //         because most of them need to modify the given tree root
   //         pointer. If these were instance member functions than
   //         that would correspond to having to modify the 'this'
   //         pointer, which is not allowed in C++. Most of the 
   //         functions that are static and which take an AVL tree
   //         pointer as a parameter are static for this reason.
   
      // Look for the given key, return NULL if not found,
      // otherwise return the item's address.
   static Comparable<KeyType> *
   Search(KeyType key, AvlNode<KeyType> * root, cmp_t cmp=EQ_CMP);

      // Insert the given key, return NULL if it was inserted,
      // otherwise return the existing item with the same key.
   static Comparable<KeyType> *
   Insert(Comparable<KeyType> * item, AvlNode<KeyType> * & root);

      // Delete the given key from the tree. Return the corresponding
      // node, or return NULL if it was not found.
   static Comparable<KeyType> *
   Delete(KeyType key, AvlNode<KeyType> * & root, cmp_t cmp=EQ_CMP);

   // Verification 

      // Return the height of this tree
   int
   Height() const;

      // Verify this tree is a valid AVL tree, return TRUE if it is,
      // return FALSE otherwise
   int
   Check() const;

      // If you want to provide your own allocation scheme than simply
      // #define the preprocessor manifest constant named CUSTOM_ALLOCATE
      // and make sure you provide and link with your own overloaded
      // versions of operators "new" and "delete" for this class.
#ifdef CUSTOM_ALLOCATE
   void *
   operator  new(size_t);

   void
   operator  delete(void *);
#endif  /* CUSTOM_ALLOCATE */


private:

   // ----- Private data

   Comparable<KeyType> * myData;  // Data field
   AvlNode<KeyType>    * mySubtree[MAX_SUBTREES];   // Pointers to subtrees
   short      myBal;   // Balance factor

      // Reset all subtrees to null and clear the balance factor
   void
   Reset(void) {
      myBal = 0 ;
      mySubtree[LEFT] = mySubtree[RIGHT] = NULL ;
   }

   // ----- Routines that do the *real* insertion/deletion

      // Insert the given key into the given tree. Return the node if
      // it already exists. Otherwise return NULL to indicate that
      // the key was successfully inserted.  Upon return, the "change"
      // parameter will be '1' if the tree height changed as a result
      // of the insertion (otherwise "change" will be 0).
   static Comparable<KeyType> *
   Insert(Comparable<KeyType> * item,
             AvlNode<KeyType> * & root,
             int & change);

      // Delete the given key from the given tree. Return NULL if the
      // key is not found in the tree. Otherwise return a pointer to the
      // node that was removed from the tree.  Upon return, the "change"
      // parameter will be '1' if the tree height changed as a result
      // of the deletion (otherwise "change" will be 0).
   static Comparable<KeyType> *
   Delete(KeyType key,
             AvlNode<KeyType> * & root,
             int & change,
             cmp_t cmp=EQ_CMP);

   // Routines for rebalancing and rotating subtrees

      // Perform an XX rotation for the given direction 'X'.
      // Return 1 if the tree height changes due to rotation,
      // otherwise return 0.
   static int
   RotateOnce(AvlNode<KeyType> * & root, dir_t dir);

      // Perform an XY rotation for the given direction 'X'
      // Return 1 if the tree height changes due to rotation,
      // otherwise return 0.
   static int
   RotateTwice(AvlNode<KeyType> * & root, dir_t dir);

      // Rebalance a (sub)tree if it has become imbalanced
   static int
   ReBalance(AvlNode<KeyType> * & root);

      // Perform a comparison of the given key against the given
      // item using the given criteria (min, max, or equivalence
      // comparison). Returns:
      //   EQ_CMP if the keys are equivalent
      //   MIN_CMP if this key is less than the item's key
      //   MAX_CMP if this key is greater than item's key
   cmp_t
   Compare(KeyType key, cmp_t cmp=EQ_CMP) const;

private:
      // Disallow copying and assignment
   AvlNode(const AvlNode<KeyType> &);
   AvlNode & operator=(const AvlNode<KeyType> &);

};


   // Class AvlTree is a simple container object to "house" an AvlNode
   // that represents the root-node of and AvlTree. Most of the member
   // functions simply delegate to the root AvlNode.
template <class KeyType>
class AvlTree {
private:
      // Disallow copying and assingment
   AvlTree(const AvlTree<KeyType> &);
   AvlTree & operator=(const AvlTree<KeyType> &);

      // Member data
   AvlNode<KeyType> * myRoot;   // The root of the tree

public:
      // Constructor and destructor
   AvlTree() : myRoot(NULL) {};
   ~AvlTree() { if (myRoot)  delete myRoot; }

      // Dump the tree to the given output stream
   void
   DumpTree(ostream & os) const;

      // See if the tree is empty
   int
   IsEmpty() const {
      return  (myRoot == NULL);
   }

      // Search, Insert, Delete, and Check
   Comparable<KeyType> *
   Search(KeyType key, cmp_t cmp=EQ_CMP) {
      return  AvlNode<KeyType>::Search(key, myRoot, cmp);
   }

   Comparable<KeyType> *
   Insert(Comparable<KeyType> * item) {
      return  AvlNode<KeyType>::Insert(item, myRoot);
   }

   Comparable<KeyType> *
   Delete(KeyType key, cmp_t cmp=EQ_CMP) {
      return  AvlNode<KeyType>::Delete(key, myRoot, cmp);
   }

   int
   Check() const {
      return  (myRoot) ? myRoot->Check() : 1;
   }
};

#endif  /* AVL_H */
