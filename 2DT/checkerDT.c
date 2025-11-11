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

