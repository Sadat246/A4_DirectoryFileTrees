/*--------------------------------------------------------------------*/
/* checkerDT.c                                                        */
/* Author: Aarush Kukreja and Hammad Farooqi                          */
/*--------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "checkerDT.h"
#include "dynarray.h"
#include "path.h"

/*
 * Checks if the given node 'oNNode' has any duplicate children.
 * 
 * Parameters:
 *   oNNode: The node to check for duplicate children.
 *
 * Returns:
 *   TRUE if 'oNNode' has no duplicate children, FALSE otherwise.
 *   If duplicate children are found, an error message is printed to stderr.
 */

static boolean CheckerDT_noDuplicateChildren(Node_T oNNode) {
   size_t ulIndex, i;
   for(ulIndex = 0; ulIndex < Node_getNumChildren(oNNode); ulIndex++)
   {
      for(i = ulIndex+1; i < Node_getNumChildren(oNNode); i++)
      {
         Node_T oNChild1 = NULL;
         Node_T oNChild2 = NULL;
         Node_getChild(oNNode, ulIndex, &oNChild1);
         Node_getChild(oNNode, i, &oNChild2);
         if (oNChild1 != NULL && oNChild2 != NULL &&
             Path_comparePath(Node_getPath(oNChild1),
                              Node_getPath(oNChild2)) == 0)
         {
            fprintf(stderr, "Node has duplicate children\n");
            return FALSE;
         }
      }
   }
   return TRUE;
}

/* see checkerDT.h for specification */
boolean CheckerDT_Node_isValid(Node_T oNNode) {
   Node_T oNParent;
   Path_T oPNPath;
   Path_T oPPPath;
   size_t ulDepth;

   /* Sample check: a NULL pointer is not a valid node */
   if(oNNode == NULL) {
      fprintf(stderr, "A node is a NULL pointer\n");
      return FALSE;
   }

   /* Sample check: parent's path must be the longest possible
      proper prefix of the node's path */
   oNParent = Node_getParent(oNNode);
   if(oNParent != NULL) {
      oPNPath = Node_getPath(oNNode);
      oPPPath = Node_getPath(oNParent);

      if(Path_getSharedPrefixDepth(oPNPath, oPPPath) !=
         Path_getDepth(oPNPath) - 1) {
         fprintf(stderr, "P-C nodes don't have P-C paths: (%s) (%s)\n",
                 Path_getPathname(oPPPath), Path_getPathname(oPNPath));
         return FALSE;
      }
   }

   /* The root node should not have a parent */
   oPNPath = Node_getPath(oNNode);
   ulDepth = Path_getDepth(oPNPath);
   if (ulDepth == 1 && oNParent != NULL) {
      fprintf(stderr, "The root node has a parent\n");
      return FALSE;
   }

   /* If it is not the root, it must have a parent */
   if (ulDepth > 1 && oNParent == NULL) {
      fprintf(stderr, "There is a non-root node without a parent\n");
      return FALSE;
   }

   /* Path should not be NULL */
   if (oPNPath == NULL) {
      fprintf(stderr, "A node has a NULL path\n");
      return FALSE;
   }

   /* The root's path should not contain a backward slash */
   if (ulDepth == 1 && strchr(Path_getPathname(oPNPath), '/')) {
      fprintf(stderr, "The root's path contains a backward slash\n");
      return FALSE;
   }

   return TRUE;
}

/*
 * Performs a pre-order traversal of the tree rooted at 'oNNode'.
 * Tracks the number of nodes in the tree using the 'pNodeCount' pointer.
 * 
 * Parameters:
 *   oNNode: The root node of the tree to traverse.
 *   pNodeCount: Pointer to a size_t variable to store the node count.
 *
 * Returns:
 *   FALSE if a broken invariant is found during the traversal, TRUE otherwise.
 *   If a broken invariant is found, an error message is printed to stderr.
 *   The 'pNodeCount' is updated with the number of nodes in the tree.
 */
static boolean CheckerDT_treeCheck(Node_T oNNode, size_t *pNodeCount) {
   size_t ulIndex;
   size_t i;

   assert(pNodeCount != NULL);

   if(oNNode != NULL) {
      (*pNodeCount)++;

      /* Sample check on each node: node must be valid */
      /* If not, pass that failure back up immediately */
      if(!CheckerDT_Node_isValid(oNNode))
         return FALSE;

      /* Check that node's children are in lexicographic order */
      for(i = 1; i < Node_getNumChildren(oNNode); i++)
      {
         Node_T oNChild1 = NULL;
         Node_T oNChild2 = NULL;
         Node_getChild(oNNode, i-1, &oNChild1); 
         Node_getChild(oNNode, i, &oNChild2);
         if (oNChild1 != NULL && oNChild2 != NULL &&
             Path_comparePath(Node_getPath(oNChild1), 
                              Node_getPath(oNChild2)) > 0)
         {
            fprintf(stderr, "Node children are not in lexicographic order\n");
            return FALSE;
         }
      }

      /* Check that node has no duplicate children */
      if(!CheckerDT_noDuplicateChildren(oNNode))
         return FALSE;

      /* Recur on every child of oNNode */
      for(ulIndex = 0; ulIndex < Node_getNumChildren(oNNode); ulIndex++)
      {
         Node_T oNChild = NULL;
         int iStatus = Node_getChild(oNNode, ulIndex, &oNChild);

         if(iStatus != SUCCESS) {
            fprintf(stderr, "getNumChildren claims more children than getChild returns\n");
            return FALSE;
         }

         /* if recurring down one subtree results in a failed check
            farther down, passes the failure back up immediately */
         if(!CheckerDT_treeCheck(oNChild, pNodeCount))
            return FALSE;
      }
   }

   return TRUE;
}

/* see checkerDT.h for specification */
boolean CheckerDT_isValid(boolean bIsInitialized, Node_T oNRoot,
                          size_t ulCount) {
   size_t nodeCount = 0;

   /* Sample check on a top-level data structure invariant:
      if the DT is not initialized, its count should be 0. */
   if(!bIsInitialized) {
      if(ulCount != 0) {
         fprintf(stderr, "Not initialized, but count is not 0\n");
         return FALSE;
      }
      if(oNRoot != NULL) {
         fprintf(stderr, "Not initialized, but root is not NULL\n");
         return FALSE;
      }
      return TRUE;
   }

   /* Check if root is NULL when ulCount > 0 */
   if(ulCount > 0 && oNRoot == NULL) {
      fprintf(stderr, "Tree is initialized, count > 0 but root is NULL\n");
      return FALSE; 
   }

   /* Now checks invariants recursively at each node from the root. */
   if(!CheckerDT_treeCheck(oNRoot, &nodeCount))
      return FALSE;

   /* Confirm node count matches ulCount */
   if(nodeCount != ulCount) {
      fprintf(stderr, "Node count does not match ulCount\n");
      return FALSE;
   }

   return TRUE;
}


// /*--------------------------------------------------------------------*/
// /* checkerDT.c                                                        */
// /* Author:                                                            */
// /*--------------------------------------------------------------------*/

// #include <assert.h>
// #include <stdio.h>
// #include <string.h>
// #include "checkerDT.h"
// #include "dynarray.h"
// #include "path.h"



// /* see checkerDT.h for specification */
// boolean CheckerDT_Node_isValid(Node_T oNNode) {
//    Node_T oNParent;
//    Path_T oPNPath;
//    Path_T oPPPath;
//    size_t nodeIndex;
//    Node_T oNNodeChild;
//    int found;
//    size_t nodeIndex2;
//    Node_T temp1;
//    size_t depth;

//    /* Sample check: a NULL pointer is not a valid node */
//    if(oNNode == NULL) {
//       fprintf(stderr, "A node is a NULL pointer\n");
//       return FALSE;
//    }
//    oPNPath = Node_getPath(oNNode);
//    if (oPNPath == NULL) {
//       fprintf(stderr,"A node has a NULL path"); /* there should be no null path*/
//       return FALSE;
//    }
//    depth = Path_getDepth(oPNPath);

//    /* Sample check: parent's path must be the longest possible
//       proper prefix of the node's path */
//    oNParent = Node_getParent(oNNode);
//    if(oNParent != NULL) {
//       oPPPath = Node_getPath(oNParent);

//       if(Path_getSharedPrefixDepth(oPNPath, oPPPath) !=
//          Path_getDepth(oPNPath) - 1) {
//          fprintf(stderr, "P-C nodes don't have P-C paths: (%s) (%s)\n",
//                  Path_getPathname(oPPPath), Path_getPathname(oPNPath));
//          return FALSE;
//       }
//    }
//    /* checks to see if node's children's parents is node with getChild and getParent*/
//    for(nodeIndex = 0; nodeIndex < Node_getNumChildren(oNNode); nodeIndex++) {
//       oNNodeChild = NULL;
//       Node_getChild(oNNode, nodeIndex, &oNNodeChild);
//       if(Node_getParent(oNNodeChild) != oNNode) {
//          fprintf(stderr, "Child's parent doesn't match parent node %s\n",
//                   Path_getPathname(Node_getPath(oNNodeChild)));
//             return FALSE;
//       }
//    }
//    /* checks to see if parent the node is contained in oNParent's children*/
//    if(oNParent != NULL) {
//       found = 0;
//       for(nodeIndex2 = 0; nodeIndex2 < Node_getNumChildren(oNParent); nodeIndex2++) {
//          temp1 = NULL;
//          Node_getChild(oNParent, nodeIndex2, &temp1);
//          if(temp1 == oNNode) found = TRUE;
//       }
//       if(!found) {
//          fprintf(stderr, "Parent does not contain child in its group of children\n");
//          return FALSE;
//       }
//    }
//    /* Path of root shouldn't contain a backward slash */
//    if (strchr(Path_getPathname(oPNPath), '/') && depth == 1) {
//       fprintf(stderr, "The path of the root contains backward slash. \n");
//       return FALSE;
//    }
//    /* if not the root, it should contain parent */
//    if (depth > 1 && oNParent == NULL) {
//       fprintf(stderr, "Non root does not contain parent\n");
//       return FALSE;
//    }
//    /* root should not contain parent */
//    if (depth == 1 && oNParent != NULL) {
//       fprintf(stderr, "Root contains parent\n");
//       return FALSE;
//    }
//    return TRUE;
// }

// /*
//    Performs a pre-order traversal of the tree rooted at oNNode.
//    Returns FALSE if a broken invariant is found and
//    returns TRUE otherwise.

//    You may want to change this function's return type or
//    parameter list to facilitate constructing your checks.
//    If you do, you should update this function comment.
// */
// static boolean CheckerDT_treeCheck(Node_T oNNode, size_t *pNodeCount) {
//    size_t ulIndex, ulIndex2, ulIndex3,ulIndex4;
//    Node_T childPrev;
//    Node_T childCurr;

//    assert(pNodeCount != NULL);
//    if(oNNode != NULL) {
//       (*pNodeCount)++;


//       /* Sample check on each node: node must be valid */
//       /* If not, pass that failure back up immediately */
//       if(!CheckerDT_Node_isValid(oNNode))
//          return FALSE;
//       /* check node's children are in lexicographic order*/
//       for(ulIndex2 = 1; ulIndex2 < Node_getNumChildren(oNNode); ulIndex2++){
//          childPrev= NULL;
//          childCurr= NULL;
//          Node_getChild(oNNode, ulIndex2-1, &childPrev); 
//          Node_getChild(oNNode, ulIndex2, &childCurr);
//          if (childPrev != NULL && childCurr != NULL &&
//              Path_comparePath(Node_getPath(childPrev), 
//                               Node_getPath(childCurr)) > 0) {
//             fprintf(stderr, "Node's children aren't in lexicographic order\n");
//             return FALSE;
//          }
//       }
//          /* checks for duplicates */
//       for(ulIndex3 = 0; ulIndex3 < Node_getNumChildren(oNNode); ulIndex3++){
//          for(ulIndex4 = ulIndex3+1; ulIndex4 < Node_getNumChildren(oNNode); ulIndex4++){
//             childPrev= NULL;
//             childCurr= NULL;
//             Node_getChild(oNNode, ulIndex3, &childPrev); 
//             Node_getChild(oNNode, ulIndex4, &childCurr);
//             if (childPrev != NULL && childCurr != NULL &&
//                Path_comparePath(Node_getPath(childPrev),
//                                  Node_getPath(childCurr)) == 0)
//             {
//                fprintf(stderr, "Node has duplicate children\n");
//                return FALSE;
//             }
//       }
//       }
//       /* Recur on every child of oNNode */
//       for(ulIndex = 0; ulIndex < Node_getNumChildren(oNNode); ulIndex++)
//       {
//          Node_T oNChild = NULL;
//          int iStatus = Node_getChild(oNNode, ulIndex, &oNChild);

//          if(iStatus != SUCCESS) {
//             fprintf(stderr, "getNumChildren claims more children than getChild returns\n");
//             return FALSE;
//          }

//          /* if recurring down one subtree results in a failed check
//             farther down, passes the failure back up immediately */
//          if(!CheckerDT_treeCheck(oNChild, pNodeCount))
//             return FALSE;
//       }

//    }
//    return TRUE;
// }

// /* see checkerDT.h for specification */
// boolean CheckerDT_isValid(boolean bIsInitialized, Node_T oNRoot,
//                           size_t ulCount) {
//    size_t nodeCount;

//    /* Sample check on a top-level data structure invariant:
//       if the DT is not initialized, its count should be 0. */
//    if(!bIsInitialized)
//       if(ulCount != 0) {
//          fprintf(stderr, "Not initialized, but count is not 0\n");
//          return FALSE;
//       }
//    /* if root is null, so should its parent*/
//    if(oNRoot != NULL && Node_getParent(oNRoot) != NULL) {
//       fprintf(stderr, "Root of tree has a non-NULL parent\n");
//       return FALSE;
//    }
//    /* similar to previous check but checks if root is null, when count should be 0*/
//    if(oNRoot == NULL && ulCount != 0) {
//       fprintf(stderr, "Root is NULL but size of tree is non-zero\n");
//       return FALSE;
//    }


//    if (!CheckerDT_treeCheck(oNRoot, &nodeCount)){
//       return FALSE;
//    }
//    /* Now checks invariants recursively at each node from the root. */
//    return CheckerDT_treeCheck(oNRoot, &nodeCount);
//    if (nodeCount != ulCount) {
//       fprintf(stderr,"Node count is not equal to ulCount\n");
//       return FALSE;
//    }
//    return TRUE;
// }
