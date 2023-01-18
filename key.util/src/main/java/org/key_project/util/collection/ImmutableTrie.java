package org.key_project.util.collection;

public class ImmutableTrie {
    private TrieNode root;

    /*@ public invariant root != null;
      @*/

    //@ ghost TrieNode[] path;
    //@ ghost int idx;

    private ImmutableTrie() {
        root = new TrieNode();
    }

    // static methods for creation

    static ImmutableTrie empty() {
        return new ImmutableTrie();
    }

    // generate tokens

    static int[] getTokensAsHexDigits(Object obj) {
        int hash = obj.hashCode();
        int bitmask = -268435456;
        int[] tokens = new int[8];for(int i = tokens.length-1; i >= 0; i--) {
            tokens[i] = (hash & bitmask) >>> (i*4);
            bitmask = bitmask >>> 4;
        }
        return tokens;
    }

    // contains-operation:

    public boolean contains(Object element) {
        int[] tokens = getTokensAsHexDigits(element);
        return contains(element, tokens);
    }

    /*@ public normal_behaviour
      @ requires tokens != null && element != null;
      @ requires (\forall int i; 0 <= i && i < tokens.length; 0 <= tokens[i] && tokens[i] < 16);
      @ ensures path[0] == root && (\forall int i; 0 <= i && i < idx; path[i].traverseEdge(tokens[i]) == path[i+1]);
      @ assignable \nothing;
      @*/
    public boolean contains(Object element, int[] tokens) {
        //@ set path = new TrieNode[tokens.length+1];
        TrieNode current = root;
        //@ set path[0] = root;
        //@ set idx = 0;
        int i = 0;
        /*@ loop_invariant 0 <= i && i <= tokens.length;
          @ loop_invariant 0 <= idx && idx <= tokens.length;
          @ loop_invariant idx <= i;
          @ loop_invariant (\forall int k; 0 <= k && k < idx; path[k].traverseEdge(tokens[k]) == path[k+1]);
          @ decreases tokens.length - i;
          @ assignable current, path[*], idx;
          @*/
        while (i < tokens.length) {
            if (current != null) {
                current = current.traverseEdge(tokens[i]);
                //@ set path[i+1] = current;
                //@ set idx = idx + 1;
            }
            i++;
        }
        if (current == null) {
            return false;
        }
        return current.containsElement(element);
    }

    // add-operation

    public ImmutableTrie add(Object element) {
        if (contains(element)) {
            return this;
        }
        int[] tokens = getTokensAsHexDigits(element);
        ImmutableTrie newTrie = new ImmutableTrie();
        TrieNode currentNewTrie = newTrie.root;
        TrieNode current = this.root;
        for (int i = 0; i < tokens.length; i++) {
            currentNewTrie.copyAndCreateNewNodeAt(tokens[i], current);
            currentNewTrie = currentNewTrie.traverseEdge(tokens[i]);
            if (current != null) {
                current = current.traverseEdge(tokens[i]);
            }
        }
        currentNewTrie.insertElement(element);
        return newTrie;
    }

    // remove-operation

    public ImmutableTrie remove(Object element) {
        if (!contains(element)) {
            return this;
        }
        int[] tokens = getTokensAsHexDigits(element);
        ImmutableTrie newTrie = new ImmutableTrie();
        TrieNode currentNewTrie = newTrie.root;
        TrieNode current = this.root;
        for (int i = 0; i < tokens.length; i++) {
            currentNewTrie.copyAndCreateNewNodeAt(tokens[i], current);
            currentNewTrie = currentNewTrie.traverseEdge(tokens[i]);
            if (current != null) {
                current = current.traverseEdge(tokens[i]);
            }
        }
        currentNewTrie.removeElement(element);
        return newTrie;
    }
}
