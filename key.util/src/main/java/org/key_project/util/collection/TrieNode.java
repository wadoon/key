package org.key_project.util.collection;

public class TrieNode {
    // public static final int ALPHABET_SIZE = 16;
    private TrieNode[] children = new TrieNode[16];
    private Object[] elements = new Object[0];

    /*@ public invariant children != null && children.length == 16;
      @ public invariant elements != null;
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= token && token < 16;
      @ ensures children[token] == null ==> \result == null;
      @ ensures children[token] != null ==> \result == children[token];
      @ assignable \nothing;
      @*/
    public /*@ nullable @*/ TrieNode traverseEdge(int token) {
        if (this.children[token] != null) {
            return this.children[token];
        } else {
            return null;
        }
    }

    /*@ public normal_behaviour
      @ requires makeCopyOf == null;
      @ ensures children[newToken] != null;
      @ assignable children[newToken];
      @
      @ also
      @
      @ public normal_behaviour
      @ requires 0 <= newToken && newToken < 16;
      @ requires makeCopyOf != null;
      @ ensures (\forall int i; 0 <= i && i < children.length && i != newToken; children[i] == makeCopyOf.children[i]);
      @ ensures elements == makeCopyOf.elements;
      @ ensures children[newToken] != null;
      @ ensures children[newToken] != makeCopyOf.children[newToken];
      @ assignable children[*], elements;
      @*/
    public void copyAndCreateNewNodeAt(int newToken, TrieNode makeCopyOf) {
        if (makeCopyOf == null) {
            this.children[newToken] = new TrieNode();
        } else {
            /*@ loop_invariant 0 <= i && i <= children.length;
              @ loop_invariant (\forall int k; 0 <= k && k < i; children[k] == makeCopyOf.children[k]);
              @ decreases children.length - i;
              @ assignable children[*];
              @*/
            for (int i = 0; i < children.length; i++) {
                this.children[i] = makeCopyOf.children[i];
            }
            TrieNode newNode = new TrieNode();
            this.children[newToken] = newNode;
            this.elements = makeCopyOf.elements;
        }
    }

    /*@ public normal_behaviour
      @ requires obj != null;
      @ ensures (\exists int n; 0 <= n && n < elements.length; elements[n] == obj) ==> \result == true;
      @ ensures (\forall int n; 0 <= n && n < elements.length; elements[n] != obj) ==> \result == false;
      @ assignable \nothing;
      @*/
    public boolean containsElement(Object obj) {
        boolean isFound = false;
        /*@ loop_invariant 0 <= i && i <= elements.length;
          @ loop_invariant (\exists int k; 0 <= k && k < i; elements[k] == obj) ==> isFound == true;
          @ loop_invariant (\forall int k; 0 <= k && k < i; elements[k] != obj) ==> isFound == false;
          @ decreases elements.length - i;
          @ assignable isFound;
          @*/
        for (int i = 0; i < elements.length; i++) {
            if (elements[i] == obj) {
                isFound = true;
            }
        }
        return isFound;
    }

    /*@ public normal_behaviour
      @ requires element != null;
      @ ensures elements.length == \old(elements).length + 1;
      @ ensures (\forall int i; 0 <= i && i < \old(elements).length; \old(elements)[i] == elements[i]);
      @ ensures elements[\old(elements).length] == element;
      @ assignable elements;
      @*/
    public void insertElement(Object element) {
        Object[] newElements = new Object[elements.length+1];
        /*@ loop_invariant 0 <= i && i <= elements.length;
          @ loop_invariant (\forall int k; 0 <= k && k < i; newElements[k] == elements[k]);
          @ decreases elements.length - i;
          @ assignable newElements[*];
          @*/
        for (int i = 0; i < elements.length; i++) {
            newElements[i] = elements[i];
        }
        newElements[elements.length] = element;
        elements = newElements;
    }

    public void removeElement(Object element) {
        if (elements.length == 0) {
            return;
        }
        boolean isFound = false;
        Object[] newElements = new Object[elements.length-1];
        for (int i = 0; i < newElements.length; i++) {
            if (elements[i] != element && !isFound) {
                newElements[i] = elements[i];
            }
            if (elements == element && !isFound) {
                isFound = true;
            }
            if (isFound) {
                newElements[i] = elements[i+1];
            }
        }
        elements = newElements;
    }

}
