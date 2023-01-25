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
      @ ensures \result == (\exists int n; 0 <= n && n < elements.length; elements[n] == obj);
      @ assignable \strictly_nothing;
      @*/
    public boolean containsElement(Object obj) {
        /*@ loop_invariant 0 <= i && i <= elements.length;
          @ loop_invariant (\forall int k; 0 <= k && k < i; elements[k] != obj);
          @ decreases elements.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < elements.length; i++) {
            if (elements[i] == obj) {
                return true;
            }
        }
        return false;
    }

    /*@ public normal_behaviour
      @ requires (\exists int n; 0 <= n && n < elements.length; elements[n] == obj);
      @ ensures \result == false;
      @ assignable \nothing;
      @
      @ also
      @
      @ public normal_behaviour
      @ requires !(\exists int n; 0 <= n && n < elements.length; elements[n] == obj);
      @ ensures elements.length == \old(elements).length + 1;
      @ ensures (\forall int i; 0 <= i && i < \old(elements).length; \old(elements)[i] == elements[i]);
      @ ensures elements[elements.length - 1] == obj;
      @ ensures \result == true;
      @ assignable elements;
      @*/
    public boolean insertElement(Object obj) {
        if (containsElement(obj)) {
            return false;
        } else {
            Object[] newElements = new Object[elements.length+1];
            /*@ loop_invariant 0 <= i && i <= elements.length;
              @ loop_invariant (\forall int k; 0 <= k && k < i; newElements[k] == elements[k]);
              @ decreases elements.length - i;
              @ assignable newElements[*];
              @*/
            for (int i = 0; i < elements.length; i++) {
                newElements[i] = elements[i];
            }
            newElements[elements.length] = obj;
            elements = newElements;
            return true;
        }
    }

    /*@ public normal_behaviour
      @ requires (\exists int n; 0 <= n && n < elements.length; elements[n] == obj);
      @ ensures elements.length == \old(elements).length - 1;
      @ ensures !(\exists int n; 0 <= n && n < elements.length; elements[n] == obj);
      @ ensures (\forall int n; 0 <= n && n < \old(getIndex(obj)); elements[n] == \old(elements)[n]);
      @ ensures (\forall int n; \old(getIndex(obj)) <= n && n < elements.length; elements[n] == \old(elements)[n + 1]);
      @ ensures \result == true;
      @ assignable elements;
      @
      @ also
      @
      @ public normal_behaviour
      @ requires !(\exists int n; 0 <= n && n < elements.length; elements[n] == obj);
      @ ensures \result == false;
      @ assignable \nothing;
      @*/
    public boolean removeElement(Object obj) {
        int index = getIndex(obj);
        if (index != -1) {
            removeElement(index);
            return true;
        } else {
            return false;
        }
    }

    /*@ public normal_behaviour
      @ requires 0 <= index && index < elements.length;
      @ ensures elements.length == \old(elements).length - 1;
      @ ensures (\forall int n; 0 <= n && n < index; elements[n] == \old(elements)[n]);
      @ ensures (\forall int n; index <= n && n < elements.length; elements[n] == \old(elements)[n + 1]);
      @ ensures !(\exists int n; 0 <= n && n < elements.length; elements[n] == \old(elements)[index]);
      @ assignable elements;
      @*/
    private void removeElement(int index) {
        Object[] newElements = new Object[elements.length-1];
        int i = 0;
        /*@ loop_invariant 0 <= i && i <= index;
          @ loop_invariant (\forall int k; 0 <= k && k < i; newElements[k] == elements[k]);
          @ decreases index - i;
          @ assignable newElements[0 .. index-1];
          @*/
        while (i < index) {
            newElements[i] = elements[i];
            i++;
        }
        /*@ loop_invariant index <= i && i <= newElements.length;
          @ loop_invariant (\forall int k; index <= k && k < i; newElements[k] == elements[k + 1]);
          @ decreases newElements.length - i;
          @ assignable newElements[index .. newElements.length-1];
          @*/
        while (i < newElements.length) {
            newElements[i] = elements[i + 1];
            i++;
        }
        elements = newElements;
    }

    /*@ public normal_behaviour
      @ ensures \result == -1 ==> !(\exists int n; 0 <= n && n < elements.length; elements[n] == obj);
      @ ensures \result != -1 ==> elements[\result] == obj && 0 <= \result && \result < elements.length
      @             && (\forall int i; 0 <= i && i < elements.length && i != \result; elements[i] != obj);
      @ assignable \strictly_nothing;
      @*/
    private int getIndex(Object obj) {
        /*@ loop_invariant 0 <= i && i <= elements.length;
          @ loop_invariant (\forall int k; 0 <= k && k < i; elements[k] != obj);
          @ decreases elements.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < elements.length; i++) {
            if (elements[i] == obj) {
                return i;
            }
        }
        return -1;
    }

}
